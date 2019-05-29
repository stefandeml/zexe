// use pairing::{
//     Engine,
//     CurveProjective
// };

// use pairing::ff::{
//     Field,
//     PrimeField
// };

use algebra::{
    Field, PairingEngine as Engine, PrimeField, ProjectiveCurve as CurveProjective, SquareRootField,
};

pub trait Group: Sized + Copy + Clone + Send + Sync {
    type ScalarField: PrimeField + SquareRootField + Into<<Self::ScalarField as PrimeField>::BigInt>;
    fn group_zero() -> Self;
    fn group_mul_assign(&mut self, by: &Self::ScalarField);
    fn group_add_assign(&mut self, other: &Self);
    fn group_sub_assign(&mut self, other: &Self);
}

pub struct Point<G: CurveProjective>(pub G);

impl<G: CurveProjective> PartialEq for Point<G> {
    fn eq(&self, other: &Point<G>) -> bool {
        self.0 == other.0
    }
}

impl<G: CurveProjective> Copy for Point<G> {}

impl<G: CurveProjective> Clone for Point<G> {
    fn clone(&self) -> Point<G> {
        *self
    }
}

impl<G: CurveProjective> Group for Point<G> {
    type ScalarField = G::ScalarField;
    fn group_zero() -> Self {
        Point(G::zero())
    }
    fn group_mul_assign(&mut self, by: &Self::ScalarField) {
        self.0.mul_assign(by.into_repr());
    }
    fn group_add_assign(&mut self, other: &Self) {
        self.0.add_assign(&other.0);
    }
    fn group_sub_assign(&mut self, other: &Self) {
        self.0.sub_assign(&other.0);
    }
}

pub struct Scalar<E: Engine>(pub E::Fr);

impl<E: Engine> PartialEq for Scalar<E> {
    fn eq(&self, other: &Scalar<E>) -> bool {
        self.0 == other.0
    }
}

impl<E: Engine> Copy for Scalar<E> {}

impl<E: Engine> Clone for Scalar<E> {
    fn clone(&self) -> Scalar<E> {
        *self
    }
}

impl<E: Engine> Group for Scalar<E> {
    type ScalarField = E::Fr;
    fn group_zero() -> Self {
        Scalar(E::Fr::zero())
    }
    fn group_mul_assign(&mut self, by: &E::Fr) {
        // self.0.mul_assign(by);
        self.0 *= by;
    }
    fn group_add_assign(&mut self, other: &Self) {
        // self.0.add_assign(&other.0);
        self.0 *= &other.0;
    }
    fn group_sub_assign(&mut self, other: &Self) {
        // self.0.sub_assign(&other.0);
        self.0 *= &other.0;
    }
}
