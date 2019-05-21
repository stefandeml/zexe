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
    utils::{AllocGadget, ConditionalEqGadget, EqGadget, ToBitsGadget, ToBytesGadget},
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

// TODO: how to make this work without using &[&AllocatedBit]
pub fn pack<E: PairingEngine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    bits: &[&AllocatedBit],
) -> Result<FpGadget<E>, SynthesisError> {
    let mut lc = LinearCombination::<E>::zero();
    let mut coeff = E::Fr::one();
    let mut acc = E::Fr::zero();

    for ref b in bits {
        let value = b.get_value().get();

        let fr: E::Fr = {
            if value.unwrap() {
                E::Fr::one()
            } else {
                E::Fr::zero()
            }
        };

        lc = lc + (coeff, b.get_variable());

        acc += &fr.mul(&coeff);
        coeff.double_in_place();
    }

    let fp = FpGadget::alloc(cs.ns(|| "packing Fp alloc"), || Ok(acc))?;

    lc = &fp.variable - lc;
    cs.enforce(|| "packing constraint", |lc| lc, |lc| lc, |_| lc);
    Ok(fp)
}

pub fn pack_bool<E: PairingEngine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<FpGadget<E>, SynthesisError> {
    let mut lc = LinearCombination::<E>::zero();
    let mut coeff = E::Fr::one();
    let mut acc = E::Fr::zero();

    let one = CS::one();
    for b in bits.iter().rev() {
        let value = b.get_value().get();

        let fr: E::Fr = {
            if value.unwrap() {
                E::Fr::one()
            } else {
                E::Fr::zero()
            }
        };

        lc = lc + b.lc(one, coeff);

        acc += &fr.mul(&coeff);
        coeff.double_in_place();
    }

    let fp = FpGadget::alloc(cs.ns(|| "packing Fp alloc"), || Ok(acc))?;

    lc = &fp.variable - lc;
    cs.enforce(|| "packing constraint", |lc| lc, |lc| lc, |_| lc);
    Ok(fp)
}

// TODO rename ...returns true if one of the bools is true
pub fn bool_false_check<E: PairingEngine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    bits: &[Boolean],
) -> Result<Boolean, SynthesisError> {
    let mut lc = LinearCombination::<E>::zero();
    let mut coeff = E::Fr::one();
    let mut acc = E::Fr::zero();

    let one = CS::one();
    for b in bits.iter() {
        let value = b.get_value().get();

        let fr: E::Fr = {
            if value.unwrap() {
                E::Fr::one()
            } else {
                E::Fr::zero()
            }
        };

        lc = lc + b.lc(one, coeff);

        acc += &fr;
    }

    let is_positive = if acc == E::Fr::zero() { true } else { false };

    let m = match is_positive {
        true => E::Fr::one(),
        false => acc.inverse().unwrap(),
    };

    // Add source for the algo!
    // X in
    // Y out
    // X*M  = Y
    // (1-Y)*X = 0

    let m = FpGadget::alloc(cs.ns(|| "bool check m alloc"), || Ok(m))?;
    let x = FpGadget::alloc(cs.ns(|| "bool check x alloc"), || Ok(acc))?;
    let b = Boolean::alloc(cs.ns(|| "alloc binary"), || Ok(!is_positive))?;

    lc = &x.variable - lc;
    cs.enforce(|| "packing constraint x", |lc| lc, |lc| lc, |_| lc);
    cs.enforce(
        || "X * M  = Y",
        |lc| &x.variable + lc,
        |lc| &m.variable + lc,
        |lc| lc + &b.lc(one, E::Fr::one()),
    );

    cs.enforce(
        || "(1-Y) * X = 0",
        |lc| &x.variable + lc,
        |lc| lc - &b.lc(one, E::Fr::one()) + CS::one(),
        |lc| lc,
    );

    Ok(b)
}

pub fn hex_to_str<E: PairingEngine>(hex_str: &str) -> Result<E::Fr, Error> {
    let str_padded = format!("{:0<64}", &hex_str);
    // TOOD: implement From<hex::FromHexError>` for `std::io::Error`
    let hex = Vec::from_hex(&str_padded).unwrap();
    Ok(E::Fr::read(&hex[..])?)
}
