use algebra::{
    bytes::FromBytes, curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator, Field,
    PairingEngine, PrimeField,
};
use hex::FromHex;
use lazy_static::lazy_static;
use regex::Regex;
use snark::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use snark_gadgets::{
    bits::boolean::AllocatedBit,
    fields::{fp::FpGadget, FieldGadget},
    test_constraint_system::TestConstraintSystem,
    utils::{AllocGadget, ConditionalEqGadget, EqGadget, ToBitsGadget, ToBytesGadget},
    Assignment,
};
use std::{
    collections::HashMap,
    fs::File,
    io::{BufRead, BufReader, Error, Write},
    ops::{Mul, Neg},
    str::FromStr,
};

enum Wire<E: PairingEngine> {
    Bit(AllocatedBit),
    Fp(FpGadget<E>),
}

pub struct PinccioReader<E: PairingEngine> {
    num_inputs:      usize,
    num_nizk_inputs: usize,
    num_outputs:     usize,

    circuit_file_name: String,
    inputs_file_name:  String,

    input_wire_ids:  Vec<usize>,
    nizk_wire_ids:   Vec<usize>,
    output_wire_ids: Vec<usize>,

    wire_values: HashMap<u64, Wire<E>>,
}

impl<E: PairingEngine> PinccioReader<E> {
    pub fn parsePinoccio(path_circuit: &str, path_inputs: &str) -> Result<Self, Error> {
        lazy_static! {
            static ref PINOCCHIO_INSTRUCTION: Regex =
                Regex::new(r"([\w|-]+) in (\d+) <([^>]+)> out (\d+) <([^>]+)>").unwrap();
        }

        let circuit_file = File::open(path_circuit)?;
        let buffered = BufReader::new(circuit_file);

        let mut lines = buffered.lines();
        let line = lines.next().unwrap()?;
        let parts: Vec<&str> = line.split(' ').collect();
        let totalWires = parts[1].parse::<usize>().unwrap();

        println!("Total wires: {}", &totalWires);

        // TODO: curently we cant make the code generic as E:Fr has no from_str!!!
        let mut cs = TestConstraintSystem::<Bls12_377>::new();
        let mut wireValues = HashMap::new();
        let mut output_wire_ids = Vec::new();

        // Read input file
        // FIXME: currently we use a BigInt and not Hex representation here!
        {
            let input_file = File::open(path_inputs)?;
            let buffered = BufReader::new(input_file);
            let mut lines = buffered.lines();
            for line in lines {
                let line = line?;
                let parts: Vec<_> = line.split(' ').collect();
                let id = parts[0].parse::<usize>().unwrap();
                let fr_str = &parts[1];
                let fr = hex_to_str::<Bls12_377>(&fr_str).unwrap();
                let fp =
                    FpGadget::alloc(cs.ns(|| format!("input for id {}", &id)), || Ok(fr)).unwrap();
                wireValues.insert(id, Wire::Fp(fp));
            }
        }

        println!("Number of inputs parsed: {}", wireValues.len());

        for line in lines {
            let line = line?;

            // jump over empty line
            if line.is_empty() {
                continue;
            };

            let (first, tail) = line.split_at(1);
            // ignore comments
            if first == "#" {
                continue;
            };

            // inputs are already allocated using inputs file
            // TODO: persist output wires to print only those (also ordered then)
            let parts: Vec<&str> = line.split(' ').collect();
            let ops = parts[0];
            if ops == "input" || ops == "nizkinput" {
                continue;
            };

            if ops == "output" {
                let wire_id = parts[1].parse::<usize>().unwrap();
                output_wire_ids.push(wire_id);
                continue;
            }

            for cap in PINOCCHIO_INSTRUCTION.captures_iter(&line) {
                // TODO: Figure out if this can be done nicely
                //     // let [ops, num_in, wires_in, num_put, wires_out] =
                // cap.iter().collect();     let lol: Vec<_> =
                // cap.iter().collect();    if let [ops, num_in, wires_in,
                // num_put, wires_out] = lol[..]{     println!("{}",
                // &ops.unwarp().as_str());    }
                let tot = &cap[0];
                let ops = &cap[1];
                let num_in = &cap[2];
                let wires_in = &cap[3];
                let num_out = &cap[4];
                let wires_out = &cap[5];
                // println!("The operation {}", &ops);

                if ops == "add" {
                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let fp_a = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };
                    let fp_b = match wireValues.get(&wires_in[1]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };

                    let res = fp_a
                        .add(cs.ns(|| format!("adding {}", &tot)), &fp_b)
                        .unwrap();

                    wireValues.insert(wires_out[0], Wire::Fp(res));
                }

                if ops == "mul" {
                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let fp_a = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };
                    let fp_b = match wireValues.get(&wires_in[1]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };

                    let res = fp_a.mul(cs.ns(|| format!("mul {}", &tot)), &fp_b).unwrap();
                    wireValues.insert(wires_out[0], Wire::Fp(res));
                }

                if ops.to_string().contains("const-mul") {
                    let is_neg = if ops == "const-mul-neg" { true } else { false };

                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let scalar = ops.to_string();
                    let scalar: Vec<_> = scalar.rsplit("-").collect();
                    let scalar = scalar[0];
                    let scalar = hex_to_str::<Bls12_377>(&scalar).unwrap();

                    let fp_a = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };

                    let res = match is_neg {
                        false => fp_a
                            .mul_by_constant(cs.ns(|| format!("mul-by-constant {}", &tot)), &scalar)
                            .unwrap(),
                        true => fp_a
                            .mul_by_constant(
                                cs.ns(|| format!("mul-by-constant {}", &tot)),
                                &scalar.neg(),
                            )
                            .unwrap(),
                    };
                    wireValues.insert(wires_out[0], Wire::Fp(res));
                }

                if ops == "split" {
                    let sign = if ops == "const-mul-neg" { true } else { false };

                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let fp = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Fp(fp) => fp,
                        _ => panic!("Found AllocatedBit"),
                    };
                    let res = fp
                        .split(cs.ns(|| format!("split {}", &tot)), wires_out.len())
                        .unwrap();

                    for (wireid, b) in wires_out.into_iter().zip(res.into_iter()) {
                        wireValues.insert(wireid, Wire::Bit(b));
                    }
                }

                if ops == "pack" {
                    let sign = if ops == "const-mul-neg" { true } else { false };

                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let mut tmp = Vec::new();

                    for wire in wires_in {
                        let b = match wireValues.get(&wire).unwrap() {
                            Wire::Bit(b) => b,
                            _ => panic!("Found Fp in packing"),
                        };

                        tmp.push(b);
                    }

                    let res = pack(cs.ns(|| format!("packing {}", &tot)), &tmp[..]).unwrap();
                    wireValues.insert(wires_out[0], Wire::Fp(res));
                }

                if ops == "or" {
                    println!("{}", &wires_in);
                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let b_a = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Bit(b) => b,
                        _ => panic!("Found Fp in or"),
                    };
                    let b_b = match wireValues.get(&wires_in[1]).unwrap() {
                        Wire::Bit(b) => b,
                        _ => panic!("Found Fp in or"),
                    };

                    let res =
                        AllocatedBit::or(cs.ns(|| format!("or {}", &tot)), &b_a, &b_b).unwrap();

                    wireValues.insert(wires_out[0], Wire::Bit(res));
                }

                if ops == "and" {
                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let b_a = match wireValues.get(&wires_in[0]).unwrap() {
                        Wire::Bit(b) => b,
                        _ => panic!(format!("Found Fp in or: {}", &tot)),
                    };
                    let b_b = match wireValues.get(&wires_in[1]).unwrap() {
                        Wire::Bit(b) => b,
                        _ => panic!(format!("Found Fp in or: {}", &tot)),
                    };

                    let res =
                        AllocatedBit::and(cs.ns(|| format!("and {}", &tot)), &b_a, &b_b).unwrap();

                    wireValues.insert(wires_out[0], Wire::Bit(res));
                }

                if ops == "assert" {
                    let wires_in: Vec<_> = wires_in
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();
                    let wires_out: Vec<_> = wires_out
                        .split(' ')
                        .map(|chunk| chunk.parse::<usize>().unwrap())
                        .collect();

                    let pair = (
                        wireValues.get(&wires_in[0]).unwrap(),
                        wireValues.get(&wires_in[1]).unwrap(),
                        wireValues.get(&wires_out[0]).unwrap(),
                    );

                    match pair {
                        (Wire::Bit(b_a), Wire::Bit(b_b), Wire::Bit(b_o)) => {
                            // WHY: warum geht das one lc + nicht?
                            cs.enforce(
                                || format!("bit_assert {}", &tot),
                                |lc| lc + b_b.get_variable(),
                                |lc| lc + b_a.get_variable(),
                                |lc| lc + b_o.get_variable(),
                            );
                            //  b_a.enforce_equal(cs.ns(|| "equal bit"), &b_b)
                        },
                        // WHY: waru geht hier die andere Reihenfolge nicht?, also lc + xx
                        (Wire::Fp(fp_a), Wire::Fp(fp_b), Wire::Fp(fp_o)) => {
                            cs.enforce(
                                || format!("fp_assert {}", &tot),
                                |lc| &fp_b.get_variable() + lc,
                                |lc| &fp_a.get_variable() + lc,
                                |lc| &fp_o.get_variable() + lc,
                            );
                        },
                        _ => panic!(format!("mixed types for assert: {}", &tot)),
                    };
                }
            }
        }

        println!("### Print all wires:");
        for (id, wire) in &wireValues {
            match wire {
                Wire::Fp(fp) => println!("Id:{}, Value {}", &id, &fp.get_value().unwrap()),
                Wire::Bit(b) => println!("Id:{}, Value {}", &id, &b.get_value().unwrap()),
            };
        }

        println!("### Print all constraints:");
        cs.print_named_objects();
        println!("Number of constraints {}", &cs.num_constraints());
        println!(
            "Is the constraint system satisfied?: {}",
            &cs.is_satisfied()
        );
        println!(
            "{}",
            &cs.which_is_unsatisfied()
                .unwrap_or("All constraints satisfied")
        );

        match output_wire_ids.len() {
            0 => println!("No output wires found"),
            _ => {
                for wire_id in output_wire_ids {
                    let wire = wireValues.get(&wire_id).unwrap();
                    match wire {
                        Wire::Fp(fp) => {
                            println!("Output id:{}, Value {}", &wire_id, &fp.get_value().unwrap())
                        },
                        Wire::Bit(b) => {
                            println!("Output id:{}, Value {}", &wire_id, &b.get_value().unwrap())
                        },
                    };
                }
            },
        };

        let circuit = PinccioReader {
            num_inputs:      0,
            num_nizk_inputs: 0,
            num_outputs:     0,

            circuit_file_name: "dasd".to_string(),
            inputs_file_name:  "String".to_string(),

            input_wire_ids:  vec![],
            nizk_wire_ids:   vec![],
            output_wire_ids: vec![],

            wire_values: HashMap::new(),
        };
        Ok(circuit)
    }
}

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
    // println!("NOT WE PACK!!");
    // println!("{}", acc);
    cs.enforce(|| "packing constraint", |lc| lc, |lc| lc, |_| lc);
    Ok(fp)
}

fn hex_to_str<E: PairingEngine>(hex_str: &str) -> Result<Fr, Error> {
    let str_padded = format!("{:0<64}", &hex_str);
    // TOOD: implement From<hex::FromHexError>` for `std::io::Error`
    let hex = Vec::from_hex(&str_padded).unwrap();
    Ok(Fr::read(&hex[..])?)
}

// TODO: delete dummy main...
fn main()  {
    println!("Hello World");
}