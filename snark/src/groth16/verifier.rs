use algebra::{
    AffineCurve as CurveAffine, PairingCurve, PairingEngine as Engine, PrimeField,
    ProjectiveCurve as CurveProjective,
};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::SynthesisError;

use std::ops::{AddAssign, Neg, Add};

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

//WHY: warum lifetime annotation necessary her?
pub fn verify_proof<E: Engine>(
    pvk: &PreparedVerifyingKey<E>,
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


pub fn batch_verify<E: Engine>(
    pvk: &PreparedVerifyingKey<E>,
    // proofs: &[&Proof<E>],
    // public_inputs: &[&[E::Fr]]
        proof1: &Proof<E>,
    public_inputs1: &[E::Fr],
        proof2: &Proof<E>,
    public_inputs2: &[E::Fr]

) -> Result<(bool, E::Fqk), SynthesisError> {

    let mut acc1 = pvk.ic[0].into_projective();
    for (i, b) in public_inputs1.iter().zip(pvk.ic.iter().skip(1)) {
        acc1.add_assign(&b.mul(i.into_repr()));
    }

    let mut acc2 = pvk.ic[0].into_projective();
    for (i, b) in public_inputs2.iter().zip(pvk.ic.iter().skip(1)) {
        acc2.add_assign(&b.mul(i.into_repr()));
    }
    let ic1 = E::pairing(acc1.into_affine().clone(), pvk.vk.gamma_g2.clone());
    let ic2 = E::pairing(acc2.into_affine().clone(), pvk.vk.gamma_g2.clone());

    let PI =  pvk.alpha_g1_beta_g2 * &ic1 * &pvk.alpha_g1_beta_g2 * &ic2;

    let ml1 = E::miller_loop(&[(&proof1.a.prepare(), &proof1.b.prepare())]);
    let ml2 = E::miller_loop(&[(&proof2.a.prepare(), &proof2.b.prepare())]);

    let mut c = proof1.c.into_projective() + &proof2.c.into_projective();
    c = c.neg();

    let cML = E::miller_loop(&[(&c.into_affine().prepare(), &pvk.vk.delta_g2.prepare())]); 
    let MC = ml1 * &ml2 * &cML;
    let F = E::final_exponentiation(&MC);

    // Ok(F.unwrap() == PI)
    let success = F.unwrap() == PI;
    Ok((success, PI))
}