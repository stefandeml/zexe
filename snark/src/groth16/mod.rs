// use pairing::{
//     Engine,
//     CurveAffine,
//     EncodedPoint
// };

use crate::SynthesisError;
use algebra::{bytes::ToBytes, PairingCurve, PairingEngine};
use std::{
    io::{self, Result as IoResult, Write},
    sync::Arc,
};
// use crate::source::SourceBuilder;
// use std::io::{self, Read, Write};
// use std::sync::Arc;
// use byteorder::{BigEndian, WriteBytesExt, ReadBytesExt};

// #[cfg(test)]
// mod tests;

mod group;
// mod singlecore;
mod generator;
mod multicore;
mod multiexp;
mod prover;
mod source;
mod verifier;
mod wnaf;
pub use self::{generator::*, prover::*, source::*, verifier::*};

#[cfg(test)]
mod test;


#[derive(Debug, Clone)]
pub struct Proof<E: PairingEngine> {
    pub a: E::G1Affine,
    pub b: E::G2Affine,
    pub c: E::G1Affine,
}

impl<E: PairingEngine> PartialEq for Proof<E> {
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a && self.b == other.b && self.c == other.c
    }
}

impl<E: PairingEngine> ToBytes for Proof<E> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> io::Result<()> {
        self.a.write(&mut writer)?;
        self.b.write(&mut writer)?;
        self.c.write(&mut writer)
    }
}

impl<E: PairingEngine> Default for Proof<E> {
    fn default() -> Self {
        Self {
            a: E::G1Affine::default(),
            b: E::G2Affine::default(),
            c: E::G1Affine::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProofInstance<'a, E: PairingEngine> {
    pub proof: Proof<E>,
    pub public_input: &'a [E::Fr]

}
// keep this for now as serialisation  might be useful and currently
// throws not implemented exception in zexe

// impl<E: PairingEngine> Proof<E> {
//     pub fn write<W: Write>(
//         &self,
//         mut writer: W
//     ) -> io::Result<()>
//     {
//         writer.write_all(self.a.into_compressed().as_ref())?;
//         writer.write_all(self.b.into_compressed().as_ref())?;
//         writer.write_all(self.c.into_compressed().as_ref())?;

//         Ok(())
//     }

//     pub fn read<R: Read>(
//         mut reader: R
//     ) -> io::Result<Self>
//     {
//         let mut g1_repr = <E::G1Affine as CurveAffine>::Compressed::empty();
//         let mut g2_repr = <E::G2Affine as CurveAffine>::Compressed::empty();

//         reader.read_exact(g1_repr.as_mut())?;
//         let a = g1_repr
//                 .into_affine()
//                 .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//                 .and_then(|e| if e.is_zero() {
//                     Err(io::Error::new(io::ErrorKind::InvalidData, "point at
// infinity"))                 } else {
//                     Ok(e)
//                 })?;

//         reader.read_exact(g2_repr.as_mut())?;
//         let b = g2_repr
//                 .into_affine()
//                 .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//                 .and_then(|e| if e.is_zero() {
//                     Err(io::Error::new(io::ErrorKind::InvalidData, "point at
// infinity"))                 } else {
//                     Ok(e)
//                 })?;

//         reader.read_exact(g1_repr.as_mut())?;
//         let c = g1_repr
//                 .into_affine()
//                 .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//                 .and_then(|e| if e.is_zero() {
//                     Err(io::Error::new(io::ErrorKind::InvalidData, "point at
// infinity"))                 } else {
//                     Ok(e)
//                 })?;

//         Ok(Proof {
//             a: a,
//             b: b,
//             c: c
//         })
//     }
// }

#[derive(Clone)]
pub struct VerifyingKey<E: PairingEngine> {
    // alpha in g1 for verifying and for creating A/C elements of
    // proof. Never the point at infinity.
    pub alpha_g1: E::G1Affine,

    // beta in g1 and g2 for verifying and for creating B/C elements
    // of proof. Never the point at infinity.
    pub beta_g1: E::G1Affine,
    pub beta_g2: E::G2Affine,

    // gamma in g2 for verifying. Never the point at infinity.
    pub gamma_g2: E::G2Affine,

    // delta in g1/g2 for verifying and proving, essentially the magic
    // trapdoor that forces the prover to evaluate the C element of the
    // proof with only components from the CRS. Never the point at
    // infinity.
    pub delta_g1: E::G1Affine,
    pub delta_g2: E::G2Affine,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / gamma
    // for all public inputs. Because all public inputs have a dummy constraint,
    // this is the same size as the number of inputs, and never contains points
    // at infinity.
    pub ic: Vec<E::G1Affine>,
}

impl<E: PairingEngine> PartialEq for VerifyingKey<E> {
    fn eq(&self, other: &Self) -> bool {
        self.alpha_g1 == other.alpha_g1
            && self.beta_g1 == other.beta_g1
            && self.beta_g2 == other.beta_g2
            && self.gamma_g2 == other.gamma_g2
            && self.delta_g1 == other.delta_g1
            && self.delta_g2 == other.delta_g2
            && self.ic == other.ic
    }
}

impl<E: PairingEngine> Default for VerifyingKey<E> {
    fn default() -> Self {
        Self {
            alpha_g1: E::G1Affine::default(),
            beta_g1:  E::G1Affine::default(),
            beta_g2:  E::G2Affine::default(),
            gamma_g2: E::G2Affine::default(),
            delta_g1: E::G1Affine::default(),
            delta_g2: E::G2Affine::default(),
            ic:       Vec::new(),
        }
    }
}

impl<E: PairingEngine> ToBytes for VerifyingKey<E> {
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
        self.alpha_g1.write(&mut writer)?;
        self.beta_g1.write(&mut writer)?;
        self.beta_g2.write(&mut writer)?;
        self.gamma_g2.write(&mut writer)?;
        self.delta_g1.write(&mut writer)?;
        self.delta_g2.write(&mut writer)?;
        for q in &self.ic {
            q.write(&mut writer)?;
        }
        Ok(())
    }
}

// keep this for now as serialisation  might be useful and currently
// throws not implemented exception in zexe
// impl<E: PairingEngine> VerifyingKey<E> {
//     pub fn write<W: Write>(
//         &self,
//         mut writer: W
//     ) -> io::Result<()>
//     {
//         writer.write_all(self.alpha_g1.into_uncompressed().as_ref())?;
//         writer.write_all(self.beta_g1.into_uncompressed().as_ref())?;
//         writer.write_all(self.beta_g2.into_uncompressed().as_ref())?;
//         writer.write_all(self.gamma_g2.into_uncompressed().as_ref())?;
//         writer.write_all(self.delta_g1.into_uncompressed().as_ref())?;
//         writer.write_all(self.delta_g2.into_uncompressed().as_ref())?;
//         writer.write_u32::<BigEndian>(self.ic.len() as u32)?;
//         for ic in &self.ic {
//             writer.write_all(ic.into_uncompressed().as_ref())?;
//         }

//         Ok(())
//     }

//     pub fn read<R: Read>(
//         mut reader: R
//     ) -> io::Result<Self>
//     {
//         let mut g1_repr = <E::G1Affine as
// CurveAffine>::Uncompressed::empty();         let mut g2_repr = <E::G2Affine
// as CurveAffine>::Uncompressed::empty();

//         reader.read_exact(g1_repr.as_mut())?;
//         let alpha_g1 = g1_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         reader.read_exact(g1_repr.as_mut())?;
//         let beta_g1 = g1_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         reader.read_exact(g2_repr.as_mut())?;
//         let beta_g2 = g2_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         reader.read_exact(g2_repr.as_mut())?;
//         let gamma_g2 = g2_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         reader.read_exact(g1_repr.as_mut())?;
//         let delta_g1 = g1_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         reader.read_exact(g2_repr.as_mut())?;
//         let delta_g2 = g2_repr.into_affine().map_err(|e|
// io::Error::new(io::ErrorKind::InvalidData, e))?;

//         let ic_len = reader.read_u32::<BigEndian>()? as usize;

//         let mut ic = vec![];

//         for _ in 0..ic_len {
//             reader.read_exact(g1_repr.as_mut())?;
//             let g1 = g1_repr
//                      .into_affine()
//                      .map_err(|e| io::Error::new(io::ErrorKind::InvalidData,
// e))                      .and_then(|e| if e.is_zero() {
//                          Err(io::Error::new(io::ErrorKind::InvalidData,
// "point at infinity"))                      } else {
//                          Ok(e)
//                      })?;

//             ic.push(g1);
//         }

//         Ok(VerifyingKey {
//             alpha_g1: alpha_g1,
//             beta_g1: beta_g1,
//             beta_g2: beta_g2,
//             gamma_g2: gamma_g2,
//             delta_g1: delta_g1,
//             delta_g2: delta_g2,
//             ic: ic
//         })
//     }
// }

#[derive(Clone)]
pub struct Parameters<E: PairingEngine> {
    pub vk: VerifyingKey<E>,

    // Elements of the form ((tau^i * t(tau)) / delta) for i between 0 and
    // m-2 inclusive. Never contains points at infinity.
    pub h: Arc<Vec<E::G1Affine>>,

    // Elements of the form (beta * u_i(tau) + alpha v_i(tau) + w_i(tau)) / delta
    // for all auxillary inputs. Variables can never be unconstrained, so this
    // never contains points at infinity.
    pub l: Arc<Vec<E::G1Affine>>,

    // QAP "A" polynomials evaluated at tau in the Lagrange basis. Never contains
    // points at infinity: polynomials that evaluate to zero are omitted from
    // the CRS and the prover can deterministically skip their evaluation.
    pub a: Arc<Vec<E::G1Affine>>,

    // QAP "B" polynomials evaluated at tau in the Lagrange basis. Needed in
    // G1 and G2 for C/B queries, respectively. Never contains points at
    // infinity for the same reason as the "A" polynomials.
    pub b_g1: Arc<Vec<E::G1Affine>>,
    pub b_g2: Arc<Vec<E::G2Affine>>,
}

impl<E: PairingEngine> PartialEq for Parameters<E> {
    fn eq(&self, other: &Self) -> bool {
        self.vk == other.vk
            && self.h == other.h
            && self.l == other.l
            && self.a == other.a
            && self.b_g1 == other.b_g1
            && self.b_g2 == other.b_g2
    }
}

// keep this for now as serialisation  might be useful and currently
// throws not implemented exception in zexe
// impl<E: PairingEngine> Parameters<E> {
//     pub fn write<W: Write>(
//         &self,
//         mut writer: W
//     ) -> io::Result<()>
//     {
//         self.vk.write(&mut writer)?;

//         writer.write_u32::<BigEndian>(self.h.len() as u32)?;
//         for g in &self.h[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.l.len() as u32)?;
//         for g in &self.l[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.a.len() as u32)?;
//         for g in &self.a[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.b_g1.len() as u32)?;
//         for g in &self.b_g1[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.b_g2.len() as u32)?;
//         for g in &self.b_g2[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         Ok(())
//     }

//     pub fn read<R: Read>(
//         mut reader: R,
//         checked: bool
//     ) -> io::Result<Self>
//     {
//         let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
//             let mut repr = <E::G1Affine as
// CurveAffine>::Uncompressed::empty();             
// reader.read_exact(repr.as_mut())?;

//             if checked {
//                 repr
//                 .into_affine()
//             } else {
//                 repr
//                 .into_affine_unchecked()
//             }
//             .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//             .and_then(|e| if e.is_zero() {
//                 Err(io::Error::new(io::ErrorKind::InvalidData, "point at
// infinity"))             } else {
//                 Ok(e)
//             })
//         };

//         let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
//             let mut repr = <E::G2Affine as
// CurveAffine>::Uncompressed::empty();             
// reader.read_exact(repr.as_mut())?;

//             if checked {
//                 repr
//                 .into_affine()
//             } else {
//                 repr
//                 .into_affine_unchecked()
//             }
//             .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//             .and_then(|e| if e.is_zero() {
//                 Err(io::Error::new(io::ErrorKind::InvalidData, "point at
// infinity"))             } else {
//                 Ok(e)
//             })
//         };

//         let vk = VerifyingKey::<E>::read(&mut reader)?;

//         let mut h = vec![];
//         let mut l = vec![];
//         let mut a = vec![];
//         let mut b_g1 = vec![];
//         let mut b_g2 = vec![];

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 h.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 l.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 a.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 b_g1.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 b_g2.push(read_g2(&mut reader)?);
//             }
//         }

//         Ok(Parameters {
//             vk: vk,
//             h: Arc::new(h),
//             l: Arc::new(l),
//             a: Arc::new(a),
//             b_g1: Arc::new(b_g1),
//             b_g2: Arc::new(b_g2)
//         })
//     }
// }

#[derive(Clone)]
pub struct PreparedVerifyingKey<E: PairingEngine> {
    // Add VerificationKey
    pub vk: VerifyingKey<E>,
    /// Pairing result of alpha*beta
    pub alpha_g1_beta_g2: E::Fqk,
    /// -gamma in G2
    pub neg_gamma_g2: <E::G2Affine as PairingCurve>::Prepared,
    /// -delta in G2
    pub neg_delta_g2: <E::G2Affine as PairingCurve>::Prepared,
    /// Copy of IC from `VerifiyingKey`.
    // TODO: delete that one!
    pub ic: Vec<E::G1Affine>,
}

impl<E: PairingEngine> From<PreparedVerifyingKey<E>> for VerifyingKey<E> {
    fn from(other: PreparedVerifyingKey<E>) -> Self {
        other.vk
    }
}

impl<E: PairingEngine> From<VerifyingKey<E>> for PreparedVerifyingKey<E> {
    fn from(other: VerifyingKey<E>) -> Self {
        prepare_verifying_key(&other)
    }
}

impl<E: PairingEngine> Default for PreparedVerifyingKey<E> {
    fn default() -> Self {
        Self {
            vk:               VerifyingKey::default(),
            alpha_g1_beta_g2: E::Fqk::default(),
            neg_gamma_g2:     <E::G2Affine as PairingCurve>::Prepared::default(),
            neg_delta_g2:     <E::G2Affine as PairingCurve>::Prepared::default(),
            ic:               Vec::new(),
        }
    }
}

impl<E: PairingEngine> Parameters<E> {
    pub fn get_vk(&self, _: usize) -> Result<VerifyingKey<E>, SynthesisError> {
        Ok(self.vk.clone())
    }

    pub fn get_h(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((&self.h[1..num_inputs], &self.h[num_inputs..]))
    }

    pub fn get_l(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((&self.l[1..num_inputs], &self.l[num_inputs..]))
    }

    pub fn get_a(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((&self.a[0..num_inputs], &self.a[num_inputs..]))
    }
    pub fn get_b_g1(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G1Affine], &[E::G1Affine]), SynthesisError> {
        Ok((&self.b_g1[0..num_inputs], &self.b_g1[num_inputs..]))
    }
    pub fn get_b_g2(
        &self,
        num_inputs: usize,
    ) -> Result<(&[E::G2Affine], &[E::G2Affine]), SynthesisError> {
        Ok((&self.b_g2[0..num_inputs], &self.b_g2[num_inputs..]))
    }
}

pub trait ParameterSource<E: PairingEngine> {
    type G1Builder: SourceBuilder<E::G1Affine>;
    type G2Builder: SourceBuilder<E::G2Affine>;

    fn get_vk(&mut self, num_ic: usize) -> Result<VerifyingKey<E>, SynthesisError>;
    fn get_h(&mut self, num_h: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_l(&mut self, num_l: usize) -> Result<Self::G1Builder, SynthesisError>;
    fn get_a(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        num_aux: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

impl<'a, E: PairingEngine> ParameterSource<E> for &'a Parameters<E> {
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(&mut self, _: usize) -> Result<VerifyingKey<E>, SynthesisError> {
        Ok(self.vk.clone())
    }

    fn get_h(&mut self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.h.clone(), 0))
    }

    fn get_l(&mut self, _: usize) -> Result<Self::G1Builder, SynthesisError> {
        Ok((self.l.clone(), 0))
    }

    fn get_a(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
    }

    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError> {
        Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
    }

    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        _: usize,
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError> {
        Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    }
}

// mod test_with_bls12_381 {
//     use super::*;
//     use crate::{Circuit, SynthesisError, ConstraintSystem};

//     use rand::{Rand, thread_rng};
//     use pairing::ff::{Field};
//     use pairing::bls12_381::{Bls12, Fr};

//     #[test]
//     fn serialization() {
//         struct MySillyCircuit<E: PairingEngine> {
//             a: Option<E::Fr>,
//             b: Option<E::Fr>
//         }

//         impl<E: PairingEngine> Circuit<E> for MySillyCircuit<E> {
//             fn synthesize<CS: ConstraintSystem<E>>(
//                 self,
//                 cs: &mut CS
//             ) -> Result<(), SynthesisError>
//             {
//                 let a = cs.alloc(|| "a", ||
// self.a.ok_or(SynthesisError::AssignmentMissing))?;                 let b =
// cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
//                 let c = cs.alloc_input(|| "c", || {
//                     let mut a =
// self.a.ok_or(SynthesisError::AssignmentMissing)?;                     let b =
// self.b.ok_or(SynthesisError::AssignmentMissing)?;

//                     a.mul_assign(&b);
//                     Ok(a)
//                 })?;

//                 cs.enforce(
//                     || "a*b=c",
//                     |lc| lc + a,
//                     |lc| lc + b,
//                     |lc| lc + c
//                 );

//                 Ok(())
//             }
//         }

//         let rng = &mut thread_rng();

//         let params = generate_random_parameters::<Bls12, _, _>(
//             MySillyCircuit { a: None, b: None },
//             rng
//         ).unwrap();

//         {
//             let mut v = vec![];

//             params.write(&mut v).unwrap();
//             assert_eq!(v.len(), 2136);

//             let de_params = Parameters::read(&v[..], true).unwrap();
//             assert!(params == de_params);

//             let de_params = Parameters::read(&v[..], false).unwrap();
//             assert!(params == de_params);
//         }

//         let pvk = prepare_verifying_key::<Bls12>(&params.vk);

//         for _ in 0..100 {
//             let a = Fr::rand(rng);
//             let b = Fr::rand(rng);
//             let mut c = a;
//             c.mul_assign(&b);

//             let proof = create_random_proof(
//                 MySillyCircuit {
//                     a: Some(a),
//                     b: Some(b)
//                 },
//                 &params,
//                 rng
//             ).unwrap();

//             let mut v = vec![];
//             proof.write(&mut v).unwrap();

//             assert_eq!(v.len(), 192);

//             let de_proof = Proof::read(&v[..]).unwrap();
//             assert!(proof == de_proof);

//             assert!(verify_proof(&pvk, &proof, &[c]).unwrap());
//             assert!(!verify_proof(&pvk, &proof, &[a]).unwrap());
//         }
//     }
// }
