use algebra::{BitIterator, Field, FpParameters, PairingEngine, PrimeField};
use snark::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
use snark_gadgets::Assignment;
use std::borrow::Borrow;

use snark_gadgets::{bits::boolean::AllocatedBit, fields::fp::FpGadget, utils::AllocGadget};
use std::{ops::Mul, str::FromStr};

enum Wire<E: PairingEngine> {
    Bit(AllocatedBit),
    Fp(FpGadget<E>),
}

pub fn pack<E: PairingEngine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    bits: &[AllocatedBit],
) -> Result<(), SynthesisError> {
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

    lc = fp.variable - lc;
    println!("NOT WE PACK!!");
    println!("{}", acc);
    cs.enforce(|| "packing constraint", |lc| lc, |lc| lc, |_| lc);
    Ok(())
    // Ok(five)
}

/// Represents a variable in the constraint system which is guaranteed
/// to be either zero or one.
#[derive(Copy, Clone, Debug)]
pub struct myAllocatedBit {
    variable: Variable,
    value:    Option<bool>,
}

impl myAllocatedBit {
    pub fn get_value(&self) -> Option<bool> {
        self.value
    }

    pub fn get_variable(&self) -> Variable {
        self.variable
    }

    // pub trait Assignment<T> {
    //     fn get(&self) -> Result<&T, SynthesisError>;
    // }

    // impl<T> Assignment<T> for Option<T> {
    //     fn get(&self) -> Result<&T, SynthesisError> {
    //         match *self {
    //             Some(ref v) => Ok(v),
    //             None => Err(SynthesisError::AssignmentMissing),
    //         }
    //     }
    // }
}

impl<E: PairingEngine> AllocGadget<bool, E> for myAllocatedBit {
    fn alloc<F, T, CS: ConstraintSystem<E>>(
        mut cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        E: PairingEngine,
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        let mut value = None;
        let var = cs.alloc(
            || "boolean",
            || {
                // value_gen? returns T -> need to get bool
                // borrow retuns &bool
                // * will dereference to bool
                value = Some(*value_gen()?.borrow());
                // Option bool
                if value.get()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(myAllocatedBit {
            variable: var,
            value,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystem<E>>(
        mut cs: CS,
        value_gen: F,
    ) -> Result<Self, SynthesisError>
    where
        E: PairingEngine,
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<bool>,
    {
        let mut value = None;
        let var = cs.alloc_input(
            || "boolean",
            || {
                // value_gen? returns T -> need to get bool
                // borrow retuns &bool
                // * will dereference to bool
                value = Some(*value_gen()?.borrow());
                // Option bool
                if value.get()? {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            },
        )?;

        // Constrain: (1 - a) * a = 0
        // This constrains a to be either 0 or 1.
        cs.enforce(
            || "boolean constraint",
            |lc| lc + CS::one() - var,
            |lc| lc + var,
            |lc| lc,
        );

        Ok(myAllocatedBit {
            variable: var,
            value,
        })
    }
}

#[cfg(test)]
mod test {

    use super::{myAllocatedBit, pack};
    use algebra::{
        curves::bls12_377::Bls12_377, fields::bls12_377::Fr, BitIterator, Field, PrimeField,
    };
    use snark::ConstraintSystem;
    use snark_gadgets::{
        bits::boolean::AllocatedBit,
        fields::{fp::FpGadget, FieldGadget},
        test_constraint_system::TestConstraintSystem,
        utils::{AllocGadget, ConditionalEqGadget, EqGadget, ToBitsGadget, ToBytesGadget},
    };
    use std::{collections::HashMap, str::FromStr};

    #[test]
    fn test_bit_allocation() {
        let mut cs = TestConstraintSystem::<Bls12_377>::new();
        let mut wireValues = HashMap::new();

        let mybit = AllocatedBit::alloc(cs.ns(|| "frist bit"), || Ok(true));
        // let mybit2 = AllocatedBit::alloc(cs.ns(|| "second bit"), || Ok(true));

        // wireValues.insert(0, mybit);

        let five =
            FpGadget::alloc(cs.ns(|| "frist fp"), || Ok(Fr::from_str("5").unwrap())).unwrap();
        let six =
            FpGadget::alloc(cs.ns(|| "second fp"), || Ok(Fr::from_str("6").unwrap())).unwrap();

        let res = five.mul(cs.ns(|| "res"), &six).unwrap();
        wireValues.insert(0, res);
        let lol = six.add(cs.ns(|| "addition"), &six).unwrap();
        wireValues.insert(1, lol);

        let mapres = wireValues.get_mut(&0).unwrap();
        let mulc = five
            .mul_by_constant(cs.ns(|| "yeah"), &Fr::from_str("10").unwrap())
            .unwrap();
        let neg = mapres.negate_in_place(cs.ns(|| "dsads"));
        println!("myhashoutput{}", mulc.get_value().unwrap());

        // / let peter = res.enforce_equal(cs.ns(|| "eq"), &res);

        let peter2 = six.split(cs.ns(|| "split"), 10usize).unwrap();

        for i in 0..10 {
            let txt = format!("split/bit {}/boolean", i);
            println!("{}", &cs.get(&txt));
        }

        let and = AllocatedBit::and(cs.ns(|| "and bits"), &peter2[1], &peter2[2]).unwrap();
        println!("{:#?}", &and.get_value());
        let peeh = pack(cs.ns(|| "sdas"), &peter2);

        // let bits = res.to_bits(cs.ns(|| "to bits"));

        // println!("{:#?}", &res.get_variable());

        println!("{:#?}", &mulc.get_value());
        println!("{:#?}", &six.get_value().unwrap().into_repr());
        println!("{:#?}", &six.get_value());
        // println!("{:#?}", &lol.get_variable());

        println!("{}", &cs.get("frist bit/boolean"));
        // println!("{}", &cs.get("second fp/alloc"));
        println!("{}", &cs.get("res/mul/alloc"));
        println!("{}", &cs.num_constraints());
        cs.print_named_objects();
        println!("{}", &cs.is_satisfied());
        println!(
            "{}",
            &cs.which_is_unsatisfied()
                .unwrap_or("all constraints satisfied")
        );
    }

}
