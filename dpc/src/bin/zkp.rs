use algebra::{
    bytes::FromBytes, curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator, Field,
    PairingEngine, PrimeField,
};
use hex::FromHex;
use lazy_static::lazy_static;
use regex::Regex;
use snark::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use snark_gadgets::{
    bits::boolean::{AllocatedBit, Boolean},
    fields::{fp::FpGadget, FieldGadget},
    test_constraint_system::TestConstraintSystem,
    utils::{
        AllocGadget, CondSelectGadget, ConditionalEqGadget, EqGadget, ToBitsGadget, ToBytesGadget,
    },
    Assignment,
};
use std::{
    collections::HashMap,
    fs::File,
    io::{BufRead, BufReader, Error, Write},
    marker::PhantomData,
    ops::{Mul, Neg},
    str::FromStr,
};

pub struct TestField<E: PairingEngine, CS: ConstraintSystem<E>> {
    dummy1: PhantomData<E>,
    dummy2: PhantomData<CS>,
}

use super::utils;

type matrix = Vec<Vec<Fr>>;
type vector = Vec<Fr>;

fn print_vec(v: &[FpGadget<Bls12_377>]) {
    for e in v {
        println!("FpGadget element: {}", &e.get_value().unwrap());
    }
}

impl<E: PairingEngine, CS: ConstraintSystem<E>> TestField<E, CS> {
    pub fn linear_layer(
        cs2: &mut CS,
        matrix: matrix,
        bias: vector,
        input: vector,
    ) -> Result<(Vec<FpGadget<Bls12_377>>), SynthesisError> {
        let mut cs = TestConstraintSystem::<Bls12_377>::new();
        const CAPACITY: usize = 253;
        const SCALING: usize = 20; // we drop the 30 least significant bits
        const RELU_CUTOFF: usize = 130; // 130 least significant bits are considered positive numbers
        let zero = Fr::zero();
        let fp_zero = FpGadget::zero(cs.ns(|| "zero element")).unwrap();

        let mut dot: Vec<FpGadget<Bls12_377>> = Vec::new();
        for (j,row) in matrix. iter(). enumerate() {
            // TODO: use map and fold!
            let mut acc = FpGadget::zero(cs.ns(|| format!("zero gadget matmul row {}", j))).unwrap();
            for (i, (x, y)) in row.iter().zip(input.iter()).enumerate() {
                let x_fp = FpGadget::alloc(cs.ns(|| format!("fpx allocation row {} element {}",j, i)), || Ok(x)).unwrap();
                let y_fp = FpGadget::alloc(cs.ns(|| format!("fpy allocation row {} element {}",j, i)), || Ok(y)).unwrap();
                let prod = &x_fp.mul(cs.ns(|| format!("matrix mul row {} element {}",j, i)), &y_fp).unwrap();
                acc = acc.add(cs.ns(|| format!("matrix mul addition row {} element {}",j, i)), &prod).unwrap();
            }
                let bias_fp = FpGadget::alloc(cs.ns(|| format!("bais allocation for row {} ",j)), || Ok(&bias[j])).unwrap();
                acc = acc.add(cs.ns(|| format!("add bias for row {}",j)), &bias_fp).unwrap();

            dot.push(acc);
        }

        // WHY: can be parallised
        let dot_bits: Vec<_> = dot
            .iter()
            .enumerate()
            .map(|(i, e)| e.to_bits(cs.ns(|| format!("bits {}", i))).unwrap())
            .collect();

        let is_negative: Vec<_> = dot_bits
            .iter()
            .enumerate()
            .map(|(i, e)| {
                utils::bool_false_check(cs.ns(|| format!("bool check {}", i)), &e[0..RELU_CUTOFF])
                    .unwrap()
            })
            .collect();
        println!("{:#?}", is_negative);

        let dot_truncated: Vec<_> = dot_bits
            .iter()
            .enumerate()
            .map(|(i, e)| {
                utils::pack_bool(cs.ns(|| format!("pack book {}", i)), &e[0..253-SCALING]).unwrap()
            })
            .collect();
        println!("{:#?}", dot_truncated);

        let out: Vec<_> = dot_truncated
            .iter()
            .zip(is_negative.iter())
            .enumerate()
            .map(|(i, (e, is_neg))| {
                FpGadget::conditionally_select(
                    cs.ns(|| format!(" cond select {}", i)),
                    is_neg,
                    &fp_zero,
                    e,
                )
                .unwrap()
            })
            .collect();
        print_vec(&out[..]);
        println!("### Print all constraints:");
        cs.print_named_objects();
        println!("Number of constraints: {}", cs.num_constraints());
        Ok(out)
    }






    pub fn run(cs2: &mut CS) -> Result<(), SynthesisError> {
        let mut cs = TestConstraintSystem::<Bls12_377>::new();
        const CAPACITY: usize = 253;
        const SCALING: usize = 30; // we drop the 30 least significant bits
        const RELU_CUTOFF: usize = 130; // 130 least significant bits are considered positive numbers
        let zero = Fr::zero();

        let five =
            FpGadget::alloc(cs.ns(|| "frist fp"), || Ok(Fr::from_str("5").unwrap())).unwrap();
        let six =
            FpGadget::alloc(cs.ns(|| "second fp"), || Ok(Fr::from_str("6").unwrap())).unwrap();

        let five_bits = five.to_bits(cs.ns(|| "to bits")).unwrap();
        let five_bits_tr = &five_bits[0..199];
        let bool_check = utils::bool_false_check(cs.ns(|| "sadsa"), &five_bits_tr).unwrap();
        println!("{:#?}", &bool_check);

        let out = FpGadget::conditionally_select(cs.ns(|| "asdsa"), &bool_check, &six, &five)?;

        let num = utils::pack_bool(cs.ns(|| "to number"), five_bits_tr).unwrap();

        println!("len {}", five_bits.len());
        println!("0{}", &five_bits[0].get_value().unwrap());
        println!("1{}", &five_bits[1].get_value().unwrap());
        println!("2{}", &five_bits[2].get_value().unwrap());
        println!("num {}", &num.get_value().unwrap());
        println!("out {}", &out.get_value().unwrap());

        println!("Hellow World");

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
}

// TODO: delete dummy main...
fn main() {
    println!("Hello World");
}
