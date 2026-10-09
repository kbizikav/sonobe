//! This module defines extension traits for elliptic curve points and their
//! in-circuit counterparts, along with some common implementations.

use ark_ec::{
    AffineRepr, CurveGroup, PrimeGroup,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_r1cs_std::{
    boolean::Boolean,
    convert::ToConstraintFieldGadget,
    fields::{FieldVar, fp::FpVar},
    groups::{CurveVar, curves::short_weierstrass::ProjectiveVar},
};
use ark_relations::gr1cs::SynthesisError;

#[cfg(feature = "evm")]
use crate::utils::evm::serialize::EVMSerialize;
use crate::{
    algebra::{
        Val,
        field::{SonobeField, emulated::EmulatedFieldVar},
        group::emulated::EmulatedAffineVar,
    },
    circuits::{WitnessToPublic, inputize::Inputize},
    transcripts::{Absorbable, AbsorbableVar},
    utils::dummy::Dummy,
};

pub mod emulated;

/// [`CF1`] is a type alias for the scalar field of a curve `C`.
pub type CF1<C> = <C as PrimeGroup>::ScalarField;
/// [`CF2`] is a type alias for the base field of a curve `C`.
pub type CF2<C> = <<C as CurveGroup>::BaseField as Field>::BasePrimeField;

/// [`SonobeCurve`] trait is a wrapper around [`CurveGroup`] that also includes
/// necessary bounds for the curve to be used conveniently in folding schemes.
pub trait SonobeCurve:
    CurveGroup<ScalarField: SonobeField, BaseField: SonobeField, Config: SWCurveConfig>
    + Absorbable
    + Val<
        Var: CurveVar<Self, Self::BaseField>
                 + AbsorbableVar<Self::BaseField>
                 + WitnessToPublic
                 + Inputize<Self::BaseField>
                 + EnforceValid,
        EmulatedVar<Self::ScalarField> = EmulatedAffineVar<Self::ScalarField, Self>,
    >
{
}

/// [`EnforceValid`] rules out the all-zero projective triple `(0, 0, 0)` in
/// in-circuit point variables.
///
/// The on-curve check performed by `ProjectiveVar::new_witness`,
/// `Z * (Y^2 - b * Z^2) = X * (X^2 + a * Z^2)`, is also satisfied by `(0, 0, 0)`,
/// which is not a projective point. The complete addition formula maps it to
/// `(0, 0, 0)` again, and `to_affine` publishes it as `(0, 0)`, the encoding of
/// the point at infinity. A prover could thus pass off `P0 + r * P1` as the
/// identity whenever `P0` is (honestly) the identity.
///
/// On the curve, `Z = 0` implies `X = 0`, so forbidding `Y = Z = 0` excludes
/// exactly the all-zero triple.
pub trait EnforceValid {
    /// [`EnforceValid::enforce_valid`] enforces that `self` is not `(0, 0, 0)`.
    fn enforce_valid(&self) -> Result<(), SynthesisError>;
}

impl<P: SWCurveConfig<BaseField: PrimeField>> EnforceValid
    for ProjectiveVar<P, FpVar<P::BaseField>>
{
    fn enforce_valid(&self) -> Result<(), SynthesisError> {
        Boolean::enforce_kary_nand(&[self.y.is_zero()?, self.z.is_zero()?])
    }
}

/// Emulated affine points have no projective representation (infinity is
/// `(0, 0)` and nothing is added to them in-circuit), so there is nothing to
/// enforce.
impl<Base: SonobeField, Target: SonobeCurve> EnforceValid for EmulatedAffineVar<Base, Target> {
    fn enforce_valid(&self) -> Result<(), SynthesisError> {
        Ok(())
    }
}

impl<P: SWCurveConfig<ScalarField: SonobeField, BaseField: SonobeField>> SonobeCurve
    for Projective<P>
{
}

impl<P: SWCurveConfig<ScalarField: SonobeField, BaseField: SonobeField>> Val for Projective<P> {
    type PreferredConstraintField = P::BaseField;
    type Var = ProjectiveVar<P, FpVar<P::BaseField>>;

    type EmulatedVar<F: SonobeField> = EmulatedAffineVar<F, Self>;
}

impl<T, C: SonobeCurve> Dummy<T> for C {
    fn dummy(_: T) -> Self {
        Default::default()
    }
}

impl<P: SWCurveConfig<BaseField: Absorbable>> Absorbable for Projective<P> {
    fn absorb_into<F: PrimeField>(&self, dest: &mut Vec<F>) {
        let affine = self.into_affine();
        let (x, y) = affine.xy().unwrap_or_default();
        [x, y].absorb_into(dest);
    }
}

impl<P: SWCurveConfig<BaseField: PrimeField>> AbsorbableVar<P::BaseField>
    for ProjectiveVar<P, FpVar<P::BaseField>>
{
    fn absorb_into(&self, dest: &mut Vec<FpVar<P::BaseField>>) -> Result<(), SynthesisError> {
        let mut vec = self.to_constraint_field()?;
        // The last element in the vector tells whether the point is infinity,
        // but we can in fact avoid absorbing it without loss of soundness.
        // This is because the `to_constraint_field` method internally invokes
        // [`ProjectiveVar::to_afine`](https://github.com/arkworks-rs/r1cs-std/blob/4020fbc22625621baa8125ede87abaeac3c1ca26/src/groups/curves/short_weierstrass/mod.rs#L160-L195),
        // which guarantees that an infinity point is represented as `(0, 0)`,
        // but the y-coordinate of a non-infinity point is never 0 (for why, see
        // https://crypto.stackexchange.com/a/108242 ).
        vec.pop();
        dest.extend(vec);
        Ok(())
    }
}

impl<P: SWCurveConfig<BaseField: PrimeField>> Inputize<P::BaseField>
    for ProjectiveVar<P, FpVar<P::BaseField>>
{
    fn inputize(value: &Self::Value) -> Vec<P::BaseField> {
        let affine = value.into_affine();
        match affine.xy() {
            Some((x, y)) => vec![x, y, One::one()],
            None => vec![Zero::zero(), One::one(), Zero::zero()],
        }
    }
}

impl<Base: SonobeField, Target: SonobeCurve> Inputize<Base> for EmulatedAffineVar<Base, Target> {
    fn inputize(value: &Self::Value) -> Vec<Base> {
        let affine = value.into_affine();
        let (x, y) = affine.xy().unwrap_or_default();
        <[EmulatedFieldVar<Base, Target::BaseField>]>::inputize(&vec![x, y])
    }
}

impl<P: SWCurveConfig<BaseField: PrimeField>> WitnessToPublic
    for ProjectiveVar<P, FpVar<P::BaseField>>
{
    fn mark_as_public(&self) -> Result<(), SynthesisError> {
        // We only need the x and y coordinates of the point, but the `infinity`
        // flag is not necessary.
        self.to_constraint_field()?[..2].mark_as_public()
    }
}

impl<Base: SonobeField, Target: SonobeCurve> WitnessToPublic for EmulatedAffineVar<Base, Target> {
    fn mark_as_public(&self) -> Result<(), SynthesisError> {
        self.x.mark_as_public()?;
        self.y.mark_as_public()?;
        Ok(())
    }
}

#[cfg(feature = "evm")]
impl<P: SWCurveConfig<BaseField: EVMSerialize>> EVMSerialize for Affine<P> {
    fn to_calldata(&self) -> Vec<u8> {
        // the encoding of the additive identity is [0, 0] on the EVM
        let (x, y) = self.xy().unwrap_or_default();

        [x.to_calldata(), y.to_calldata()].concat()
    }
}

#[cfg(feature = "evm")]
impl<P: SWCurveConfig<BaseField: EVMSerialize>> EVMSerialize for Projective<P> {
    fn to_calldata(&self) -> Vec<u8> {
        self.into_affine().to_calldata()
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::{Fq, G1Projective as G1, g1::Config};
    use ark_r1cs_std::{alloc::AllocVar, groups::curves::short_weierstrass::ProjectiveVar};
    use ark_relations::gr1cs::ConstraintSystem;
    use ark_std::{UniformRand, rand::thread_rng};

    use super::*;

    type PVar = ProjectiveVar<Config, FpVar<Fq>>;

    fn satisfied_after_enforcing(x: Fq, y: Fq, z: Fq) -> bool {
        let cs = ConstraintSystem::<Fq>::new_ref();
        let p = PVar::new(
            FpVar::new_witness(cs.clone(), || Ok(x)).unwrap(),
            FpVar::new_witness(cs.clone(), || Ok(y)).unwrap(),
            FpVar::new_witness(cs.clone(), || Ok(z)).unwrap(),
        );
        p.enforce_valid().unwrap();
        cs.is_satisfied().unwrap()
    }

    #[test]
    fn test_enforce_valid() {
        let mut rng = thread_rng();
        let (x, y) = G1::rand(&mut rng).into_affine().xy().unwrap();
        let z = Fq::rand(&mut rng);

        // a finite point (also with a non-normalised `z`) and the point at infinity are accepted
        assert!(satisfied_after_enforcing(x, y, Fq::one()));
        assert!(satisfied_after_enforcing(x * z, y * z, z));
        assert!(satisfied_after_enforcing(Fq::zero(), Fq::one(), Fq::zero()));
        assert!(satisfied_after_enforcing(Fq::zero(), z, Fq::zero()));
        // the all-zero triple is not a point
        assert!(!satisfied_after_enforcing(Fq::zero(), Fq::zero(), Fq::zero()));
    }

    /// `(0, 0, 0)` passes the on-curve check of `ProjectiveVar`, which is why
    /// [`EnforceValid`] is needed.
    #[test]
    fn test_zero_triple_passes_on_curve_check() {
        let cs = ConstraintSystem::<Fq>::new_ref();
        let zero = || FpVar::new_witness(cs.clone(), || Ok(Fq::zero())).unwrap();
        let (x, y, z) = (zero(), zero(), zero());
        // Z * (Y^2 - b Z^2) = X * (X^2 + a Z^2) as in `new_variable_omit_prime_order_check`
        let b = <Config as SWCurveConfig>::COEFF_B;
        let a = <Config as SWCurveConfig>::COEFF_A;
        let rhs = &x * (x.square().unwrap() + z.square().unwrap() * a);
        z.mul_equals(&(y.square().unwrap() - z.square().unwrap() * b), &rhs)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
