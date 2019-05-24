use algebra::{
    AffineCurve as CurveAffine, PairingCurve, PairingEngine as Engine, PrimeField,
    ProjectiveCurve as CurveProjective,
};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::SynthesisError;

use std::ops::{AddAssign, Neg};

pub fn prepare_verifying_key<E: Engine>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let mut gamma = vk.gamma_g2;
    gamma = gamma.neg();
    let mut delta = vk.delta_g2;
    delta = delta.neg();

    PreparedVerifyingKey {
        vk:               vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2),
        neg_gamma_g2:     gamma.prepare(),
        neg_delta_g2:     delta.prepare(),
        ic:               vk.ic.clone(),
    }
}

pub fn verify_proof<'a, E: Engine>(
    pvk: &'a PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.ic.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut acc = pvk.ic[0].into_projective();

    // 1 scalar mul + 1 additon per public input!
    for (i, b) in public_inputs.iter().zip(pvk.ic.iter().skip(1)) {
        acc.add_assign(&b.mul(i.into_repr()));
    }
    // vk_x

    // groth16 verification 4-pair paring check
    // proof.A, proof.B,
    // Pairing.negate(vk_x), vk.gamma,
    // Pairing.negate(proof.C), vk.delta,
    // Pairing.negate(vk.a), vk.b))

    // Multi_miller loop + final exp
    Ok(E::final_exponentiation(&E::miller_loop(
        [
            (&proof.a.prepare(), &proof.b.prepare()),
            (&acc.into_affine().prepare(), &pvk.neg_gamma_g2),
            (&proof.c.prepare(), &pvk.neg_delta_g2),
        ]
        .into_iter(),
    ))
    .unwrap()
        == pvk.alpha_g1_beta_g2)
}
