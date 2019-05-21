use algebra::{bytes::ToBytes, Field, FpParameters, PairingEngine, PrimeField};

pub mod pinoccio;

use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator};
use lazy_static::lazy_static;
use snark::ConstraintSystem;
use snark_gadgets::test_constraint_system::TestConstraintSystem;
use std::{
    fs::File,
    io::{BufRead, BufReader, Error, Write},
};

fn main() -> Result<(), Error> {
    let path_circuit = "src/bin/circuit.arith";
    let path_inputs = "src/bin/inputs.arith";
    let mut cs = TestConstraintSystem::<Bls12_377>::new();

    // WHY?: Warum kann ich hier keinen Namespace verwenden?w
    let circuit =
        pinoccio::PinccioReader::<Bls12_377, TestConstraintSystem<Bls12_377>>::parsePinoccio(
            &mut cs,
            &path_circuit,
            &path_inputs,
        );
    let res = circuit.unwrap();

    println!("### Print all constraints:");
    cs.print_named_objects();
    println!(
        "Is the constraint system satisfied?: {}",
        &cs.is_satisfied()
    );
    println!(
        "{}",
        &cs.which_is_unsatisfied()
            .unwrap_or("All constraints satisfied")
    );

    Ok(())
}
