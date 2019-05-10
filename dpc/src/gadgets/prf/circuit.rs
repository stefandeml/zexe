
#![allow(unused_imports)]
#![allow(unused_variables)]

// use bellman::pairing;
// use pairing::ParingEngine;
// use bellman::{Circuit, ConstraintSystem, SynthesisError};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
// use pairing::bls12_381::{Fr};
// use sapling_crypto::circuit::{blake2s, boolean, ecc, multipack, num, Assignment};
// use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};


use super::myblake2::blake2s;

use snark::{
    gm17::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    },
    Circuit, ConstraintSystem, SynthesisError,
};
use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr, PairingEngine};
use rand::{thread_rng, Rand};

use snark_gadgets::{
    boolean::{AllocatedBit, Boolean},
    utils::{AllocGadget, ConditionalEqGadget, ConditionalOrEqualsGadget, ToBytesGadget},
};



// We have some dummy input variable.
#[derive(Debug, Clone, Copy)]
pub struct Blake2sBench<E: PairingEngine> {
    pub num_bytes: i32,
    pub dummy: Option<E::Fr>,
}

impl<E: PairingEngine> Circuit<E> for Blake2sBench<E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        use rand::{Rng, SeedableRng, XorShiftRng};
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        // Allocate the dummy value
        let a = cs.alloc_input(|| "dummy", || {
            self.dummy.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let input_len = self.num_bytes;
        let data: Vec<u8> = (0..input_len).map(|_| rng.gen()).collect();
        println!("#Number of bytes: {}", data.len());

        let mut input_bits = vec![];

        for (byte_i, input_byte) in data.into_iter().enumerate() {
            for bit_i in 0..8 {
                let cs = cs.ns(|| format!("input bit {} {}", byte_i, bit_i));

                input_bits.push(
                    AllocatedBit::alloc(cs, || Ok((input_byte >> bit_i) & 1u8 == 1u8))
                        .unwrap()
                        .into(),
                );
            }
        }

        let hash = blake2s(
            cs.ns(|| "calculate hash"),
            &input_bits,
            b"12345678",
        )?;

        Ok(())
    }
}

mod test{
use rand::{thread_rng, Rand};
use snark::{
    // gm17::{
    groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    },
    Circuit, ConstraintSystem, SynthesisError,
};
use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr};

    use super::Blake2sBench;

    #[test]
    fn prove_and_verify_cicruit() {

        let rng = &mut thread_rng();

        let params = {
            let c = Blake2sBench::<Bls12_377> {
                num_bytes: 192,
                dummy: None,
            };

            generate_random_parameters(c, rng).unwrap()
        };

        let pvk = prepare_verifying_key::<Bls12_377>(&params.vk);

        let dummy = Some(Fr::rand(rng)); 
        // Create an instance of circuit
        let c = Blake2sBench::<Bls12_377> {
            num_bytes: 192,
            dummy: dummy,
        };

        // Create a groth16 proof with our parameters.
        let proof = create_random_proof(c, &params, rng).unwrap();

        assert!(verify_proof(&pvk, &proof, &[dummy.unwrap()]).unwrap());

        }
    }
