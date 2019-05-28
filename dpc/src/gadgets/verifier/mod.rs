use algebra::PairingEngine;
use snark::{ConstraintSystem, SynthesisError};

use crate::crypto_primitives::nizk::NIZK;
use snark_gadgets::utils::{AllocGadget, ToBitsGadget, ToBytesGadget};

pub mod gm17;
pub mod groth16;
pub mod groth16batch;

pub trait NIZKVerifierGadget<N: NIZK, E: PairingEngine> {
    type VerificationKeyGadget: AllocGadget<N::VerificationParameters, E> + ToBytesGadget<E>;

    type ProofGadget: AllocGadget<N::Proof, E>;

    fn check_verify<'a, CS, I, T>(
        cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        input: I,
        proof: &Self::ProofGadget,
    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
        I: Iterator<Item = &'a T>,
        T: 'a + ToBitsGadget<E> + ?Sized;
}

pub trait NIZKBatchVerifierGadget<N: NIZK, E: PairingEngine, PairingE: PairingEngine> {
    type VerificationKeyGadget: AllocGadget<N::VerificationParameters, E> + ToBytesGadget<E>;

    type ProofGadget: AllocGadget<N::Proof, E>;

    // type ParingE: N::PairingEngine;

    fn check_batch_verify<'a, CS, I, T>(
        cs: CS,
        verification_key: &Self::VerificationKeyGadget,
        public_inputs: &mut [I],
        proof_gadgets: &[Self::ProofGadget],
        PI: PairingE::Fqk

    ) -> Result<(), SynthesisError>
    where
        CS: ConstraintSystem<E>,
        I: Iterator<Item = &'a T>,
        T: 'a + ToBitsGadget<E> + ?Sized,;
}