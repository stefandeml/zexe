// we need this version for multi base scalar multiexp to have  density support

use algebra::{
    AffineCurve as CurveAffine, BigInteger, Field, PairingCurve, PairingEngine, PrimeField,
    ProjectiveCurve as CurveProjective,
};

use super::{singlecore::Worker, source::*};
use crate::SynthesisError;
use futures::Future;
use std::sync::Arc;

/// This genious piece of code works in the following way:
/// - choose `c` - the bit length of the region that one thread works on
/// - make `2^c - 1` buckets and initialize them with `G = infinity` (that's
///   equivalent of zero)
/// - there is no bucket for "zero" cause it's not necessary
/// - go over the pairs `(base, scalar)`
/// - for each scalar calculate `scalar % 2^c` and add the base (without any
///   multiplications!) to the
/// corresponding bucket
/// - at the end each bucket will have an accumulated value that should be
///   multiplied by the corresponding factor
/// between `1` and `2^c - 1` to get the right value
/// - here comes the first trick - you don't need to do multiplications at all,
///   just add all the buckets together
/// starting from the first one `(a + b + c + ...)` and than add to the first
/// sum another sum of the form `(b + c + d + ...)`, and than the third one `(c
/// + d + ...)`, that will result in the proper prefactor infront of every
/// accumulator, without any multiplication operations at all
/// - that's of course not enough, so spawn the next thread
/// - this thread works with the same bit width `c`, but SKIPS lowers bits
///   completely, so it actually takes values
/// in the form `(scalar >> c) % 2^c`, so works on the next region
/// - spawn more threads until you exhaust all the bit length
/// - you will get roughly `[bitlength / c] + 1` inaccumulators
/// - double the highest accumulator enough times, add to the next one, double
///   the result, add the next accumulator, continue
///
/// Demo why it works:
/// ```
///     a * G + b * H = (a_2 * (2^c)^2 + a_1 * (2^c)^1 + a_0) * G + (b_2 * (2^c)^2 + b_1 * (2^c)^1 + b_0) * H
/// ```
/// - make buckets over `0` labeled coefficients
/// - make buckets over `1` labeled coefficients
/// - make buckets over `2` labeled coefficients
/// - accumulators over each set of buckets will have an implicit factor of
///   `(2^c)^i`, so before summing thme up
/// "higher" accumulators must be doubled `c` times
#[allow(dead_code)]
fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::ScalarField as PrimeField>::BigInt>>,
    mut skip: u32,
    c: u32,
    handle_trivial: bool,
) -> Box<dyn Future<Item = <G as CurveAffine>::Projective, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PairingCurve,
    S: SourceBuilder<G>,
{
    // Perform this region of the multiexp
    let this = {
        let bases = bases.clone();
        let exponents = exponents.clone();
        let density_map = density_map.clone();

        // This looks like a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::zero().into_projective();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            // let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            // let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();
            // let zero = G::zero().into_projective();
            let one = <G::Engine as PairingEngine>::Fr::one().into_repr(); // let one = <G::Engine as PairingEngine>::Fr::one().into_repr();
                                                                           // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                // Go over density and exponents
                if density {
                    if exp.is_zero() {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        // exp.shr(skip);
                        exp.divn(skip);
                        let exp = exp.as_ref()[0] % (1 << c);

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum += &exp;
                acc += &running_sum;
            }

            Ok(acc)
        })
    };

    skip += c;

    if skip >= <G::ScalarField as PrimeField>::size_in_bits() as u32 {
        // There isn't another region.
        Box::new(this)
    } else {
        // There's another region more significant. Calculate and join it with
        // this region recursively.
        Box::new(
            this.join(multiexp_inner(
                pool,
                bases,
                density_map,
                exponents,
                skip,
                c,
                false,
            ))
            .map(move |(this, mut higher)| {
                for _ in 0..c {
                    higher.double_in_place();
                }

                higher += &this;

                higher
            }),
        )
    }
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
#[allow(dead_code)]
pub fn multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::ScalarField as PrimeField>::BigInt>>,
) -> Box<dyn Future<Item = <G as CurveAffine>::Projective, Error = SynthesisError>>
where
    for<'a> &'a Q: QueryDensity,
    D: Send + Sync + 'static + Clone + AsRef<Q>,
    G: PairingCurve,
    S: SourceBuilder<G>,
{
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.

        assert!(query_size == exponents.len());
    }

    multiexp_inner(pool, bases, density_map, exponents, 0, c, true)
}

#[test]
fn test_with_bls12() {
    fn naive_multiexp<G: CurveAffine>(
        bases: Arc<Vec<G>>,
        exponents: Arc<Vec<<G::ScalarField as PrimeField>::BigInt>>,
    ) -> G::Projective {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::Projective::zero();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            acc += &base.mul(*exp);
        }

        acc
    }

    use algebra::curves::bls12_381::Bls12_381;
    use rand::{self, Rand, SeedableRng, XorShiftRng};
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    const SAMPLES: usize = 1 << 9;

    let v = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12_381 as PairingEngine>::Fr::rand(&mut rng).into_repr())
            .collect::<Vec<_>>(),
    );
    let g = Arc::new(
        (0..SAMPLES)
            .map(|_| <Bls12_381 as PairingEngine>::G1Projective::rand(&mut rng).into_affine())
            .collect::<Vec<_>>(),
    );

    let naive = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = multiexp(&pool, (g, 0), FullDensity, v).wait().unwrap();

    assert_eq!(naive, fast);
}
