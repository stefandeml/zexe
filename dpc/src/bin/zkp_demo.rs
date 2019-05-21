use algebra::{bytes::ToBytes, Field, FpParameters, PairingEngine, PrimeField};

pub mod pinoccio;
pub mod utils;
pub mod zkp;
use utils::pack;

use algebra::{curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator};
use lazy_static::lazy_static;
use snark::ConstraintSystem;
use snark_gadgets::test_constraint_system::TestConstraintSystem;
use std::{
    fs::File,
    io::{BufRead, BufReader, Error, Write},
    ops::Neg,
    str::FromStr,
};

fn read_marix(path: &str) -> Result<Vec<Vec<Fr>>, Error> {
    let file = File::open(&path)?;
    let buffered = BufReader::new(file);
    let mut reader = csv::ReaderBuilder::new()
        .has_headers(false)
        .from_reader(buffered);

    let mut m = Vec::new();
    for record in reader.records() {
        let record = record?;
        let entry: Vec<_> = record.iter().map(|x| str_to_fr(&x)).collect();
        m.push(entry);
    }
    Ok(m)
}

fn read_vector(path: &str) -> Result<Vec<Fr>, Error> {
    let file = File::open(&path)?;
    let buffered = BufReader::new(file);
    let mut reader = csv::ReaderBuilder::new()
        .has_headers(false)
        .from_reader(buffered);

    let mut m = Vec::new();
    for record in reader.records() {
        let record = record?;
        m.push(str_to_fr(&record[0]));
    }
    Ok(m)
}

fn str_to_fr(s: &str) -> Fr {
    let s = s.to_string();
    let is_negative = s.starts_with("-");
    let fr = match is_negative {
        true => {
            let (s, i) = s.split_at(1);
            Fr::from_str(&i).unwrap().neg()
        },
        false => Fr::from_str(&s).unwrap(),
    };
    fr
}

fn main() -> Result<(), Error> {
    let mut cs = TestConstraintSystem::<Bls12_377>::new();

    let path_A = "src/bin/A.csv";
    let A = read_marix(&path_A)?;

    let path_a_bias = "src/bin/a_bias.csv";
    let a_bias = read_vector(&path_a_bias)?;

    let path_input = "src/bin/input.csv";
    let input = read_vector(&path_input)?;

    let lol = "2321";
    let fr = str_to_fr(&lol);
    let circuit = zkp::TestField::<Bls12_377, TestConstraintSystem<Bls12_377>>::linear_layer(
        &mut cs, A, a_bias, input,
    );

    println!("{}", &fr);

    // println!("### Print all constraints:");
    // cs.print_named_objects();
    // println!(
    //     "Is the constraint system satisfied?: {}",
    //     &cs.is_satisfied()
    // );
    // println!(
    //     "{}",
    //     &cs.which_is_unsatisfied()
    //         .unwrap_or("All constraints satisfied")
    // );

    Ok(())
}
