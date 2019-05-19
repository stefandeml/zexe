use algebra::{bytes::ToBytes, Field, FpParameters, PairingEngine, PrimeField};

pub mod pinoccio;

use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator};
use lazy_static::lazy_static;
use std::{
    fs::File,
    io::{BufRead, BufReader, Error, Write},
};

fn main() -> Result<(), Error> {
    let path_circuit = "src/bin/circuit.arith";
    let path_inputs = "src/bin/inputs.arith";

    let circuit = pinoccio::PinccioReader::<Bls12_377>::parsePinoccio(&path_circuit, &path_inputs);
    let res = circuit.unwrap();

    Ok(())
}
