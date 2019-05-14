        use snark::{ConstraintSystem, LinearCombination, SynthesisError, Variable};
        use algebra::{BitIterator, Field, FpParameters, PairingEngine, PrimeField};
        use std::borrow::Borrow;
        use snark_gadgets::Assignment;

        use snark_gadgets::utils::AllocGadget;

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

        impl<E: PairingEngine> AllocGadget<bool,E> for myAllocatedBit{

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
                                |lc| lc  - var,
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
mod test{

    use super::myAllocatedBit;
    use snark_gadgets::{
        test_constraint_system::TestConstraintSystem,
        utils::{AllocGadget, ConditionalEqGadget, EqGadget, ToBytesGadget},
    };
   use algebra::{
        curves::bls12_381::Bls12_381, fields::bls12_381::Fr, BitIterator, Field, PrimeField,
    };    
    use snark::ConstraintSystem;
    use std::str::FromStr;

    #[test]
    fn test_bit_allocation() {
        let mut cs = TestConstraintSystem::<Bls12_381>::new();
        {
        let mut cs_new = cs.ns(|| format!("input bit eins"));
        let mybit = myAllocatedBit::alloc(&mut cs_new, || Ok(false));
        }
        {
        let mut cs_new2 = cs.ns(|| format!("input bit zwei"));
        let mybit = myAllocatedBit::alloc(&mut cs_new2, || Ok(true));
        }
        println!("{}", &cs.get("input bit zwei/boolean"));
        println!("{}", &cs.num_constraints());
        cs.print_named_objects();
        println!("{}", &cs.is_satisfied());
        println!("{}", &cs.which_is_unsatisfied().unwrap());
    }

}