
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
    gm17::{
    // groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    },
    Circuit, ConstraintSystem, SynthesisError,
};
    use algebra::{curves::sw6::SW6, fields::sw6::Fr as Fr_SW6};
    use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr as Fr_Bls12_377};
    use algebra::{curves::bls12_381::Bls12_381, fields::bls12_381::Fr as Fr_Bls12_381};
    use super::Blake2sBench;

    #[test]
    fn prove_and_verify_blake2s_cicruit_bls12_377() {
        
        type Curve = Bls12_377;
        type Fr = Fr_Bls12_377;
        let num_bytes = 384;
        let rng = &mut thread_rng();
        let setup_time = timer_start!(|| "{Bls12_377}::Setup");
        let params = {
            let c = Blake2sBench::<Curve> {
                num_bytes: num_bytes,
                dummy: None,
            };
            generate_random_parameters(c, rng).unwrap()
        };
        timer_end!(setup_time);

        let prep_vk_time = timer_start!(|| "{Bls12_377}::Verification Key");
        let pvk = prepare_verifying_key::<Curve>(&params.vk);
        timer_end!(prep_vk_time);

        let dummy = Some(Fr::rand(rng)); 
        // Create an instance of circuit
        let c = Blake2sBench::<Curve> {
            num_bytes: num_bytes,
            dummy: dummy,
        };

        // Create a groth16 proof with our parameters.
        let proof_time = timer_start!(|| "{Bls12_377}::Generate Proof");
        let proof = create_random_proof(c, &params, rng).unwrap();
        timer_end!(proof_time);

        assert!(verify_proof(&pvk, &proof, &[dummy.unwrap()]).unwrap());

    }

    #[test]
    fn prove_and_verify_blake2s_cicruit_bls12_381() {
        
        type Curve = Bls12_381;
        type Fr = Fr_Bls12_381;
        let num_bytes = 384;        
        let rng = &mut thread_rng();
        let setup_time = timer_start!(|| "{Bls12_381}::Setup");
        let params = {
            let c = Blake2sBench::<Curve> {
                num_bytes: num_bytes,
                dummy: None,
            };
            generate_random_parameters(c, rng).unwrap()
        };
        timer_end!(setup_time);

        let prep_vk_time = timer_start!(|| "{Bls12_381}::Verification Key");
        let pvk = prepare_verifying_key::<Curve>(&params.vk);
        timer_end!(prep_vk_time);

        let dummy = Some(Fr::rand(rng)); 
        // Create an instance of circuit
        let c = Blake2sBench::<Curve> {
            num_bytes: num_bytes,
            dummy: dummy,
        };

        // Create a groth16 proof with our parameters.
        let proof_time = timer_start!(|| "{Bls12_381}::Generate Proof");
        let proof = create_random_proof(c, &params, rng).unwrap();
        timer_end!(proof_time);

        assert!(verify_proof(&pvk, &proof, &[dummy.unwrap()]).unwrap());

    }
    #[test]
    fn prove_and_verify_blake2s_cicruit_sw6() {
        
        type Curve = SW6;;
        type Fr = Fr_SW6;
        let num_bytes = 3072;        
        let rng = &mut thread_rng();
        let setup_time = timer_start!(|| "{SW6}::Setup");
        let params = {
            let c = Blake2sBench::<Curve> {
                num_bytes: num_bytes,
                dummy: None,
            };
            generate_random_parameters(c, rng).unwrap()
        };
        timer_end!(setup_time);

        let prep_vk_time = timer_start!(|| "{SW6}::Verification Key");
        let pvk = prepare_verifying_key::<Curve>(&params.vk);
        timer_end!(prep_vk_time);

        let dummy = Some(Fr::rand(rng)); 
        // Create an instance of circuit
        let c = Blake2sBench::<Curve> {
            num_bytes: num_bytes,
            dummy: dummy,
        };

        // Create a groth16 proof with our parameters.
        let proof_time = timer_start!(|| "{SW6}::Generate Proof");
        let proof = create_random_proof(c, &params, rng).unwrap();
        timer_end!(proof_time);

        assert!(verify_proof(&pvk, &proof, &[dummy.unwrap()]).unwrap());

    }

    }
