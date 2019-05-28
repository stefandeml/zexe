use algebra::{
    AffineCurve as CurveAffine, PairingCurve, PairingEngine as Engine, PrimeField,
    ProjectiveCurve as CurveProjective,
};

use super::{PreparedVerifyingKey, Proof, VerifyingKey, ProofInstance};

use crate::SynthesisError;

use std::ops::{AddAssign, Neg, Add};

use algebra::fields::Field;

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

pub fn verify_proof<E: Engine>(
    pvk: &PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<bool, SynthesisError> {
    if (public_inputs.len() + 1) != pvk.ic.len() {
        return Err(SynthesisError::MalformedVerifyingKey);
    }

    let mut acc = pvk.ic[0].into_projective();

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


pub fn batch_verify<'a, E: Engine>(
    pvk: &PreparedVerifyingKey<E>,
    proof_instances: &'a [ProofInstance<E>]
) -> Result<(bool, E::Fqk), SynthesisError> {

    let mut ics = Vec::new();
    let mut ml_ab = Vec::new();
    let mut c_acc = E::G1Projective::zero();

    for pf in proof_instances {
        let ProofInstance {proof, public_input} = pf;

        let mut ic = pvk.ic[0].into_projective();
        for (i, b) in public_input.iter().zip(pvk.ic.iter().skip(1)) {
            ic.add_assign(&b.mul(i.into_repr()));
    }
        let ic = E::pairing(ic.into_affine().clone(), pvk.vk.gamma_g2.clone());
        ics.push(ic);

        c_acc +=  &proof.c.into_projective();

        let ml = E::miller_loop(&[(&proof.a.prepare(), &proof.b.prepare())]);
        ml_ab.push(ml);
    }

    let mut PI = pvk.alpha_g1_beta_g2 * &ics[0];
    for ic in ics.iter().skip(1) {
        PI *=  &pvk.alpha_g1_beta_g2;
        PI *=  &ic;
    };

    c_acc = c_acc.neg();
    let cML = E::miller_loop(&[(&c_acc.into_affine().prepare(), &pvk.vk.delta_g2.prepare())]); 

    let mut MC = cML;
    for i in ml_ab  {
        MC *= &i
    };

    let F = E::final_exponentiation(&MC);

    let success = F.unwrap() == PI;
    Ok((success, PI))
}