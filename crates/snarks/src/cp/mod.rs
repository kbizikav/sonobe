//! Abstract trait and implementations for commit-and-prove SNARKs.

use ark_ff::Field;
use ark_std::{borrow::Borrow, rand::RngCore};

pub mod legogroth16;

/// [`CPSNARK`] defines a commit-and-prove SNARK, i.e., a SNARK for a relation
/// `R(x, w)` whose proof additionally attests that (part of) the witness `w` is
/// the message of a list of externally given commitments.
pub trait CPSNARK {
    /// [`CPSNARK::Field`] is the field over which the public inputs and the
    /// witness are defined.
    type Field: Field;

    /// [`CPSNARK::Relation`] is the description of the relation (e.g., a
    /// constraint system and which of its witness variables are committed) for
    /// which the keys are generated.
    type Relation;

    /// [`CPSNARK::CommitmentKey`] is the key of the commitment scheme for the
    /// external commitments.
    type CommitmentKey;
    /// [`CPSNARK::CommitmentOpening`] is the opening (randomness) of an
    /// external commitment.
    type CommitmentOpening;
    /// [`CPSNARK::Commitment`] is the type of an external commitment.
    type Commitment;

    /// [`CPSNARK::ProverKey`] is the proving key.
    type ProverKey;
    /// [`CPSNARK::VerifierKey`] is the verifying key.
    type VerifierKey;

    /// [`CPSNARK::Proof`] is the proof.
    type Proof;

    /// [`CPSNARK::Error`] is the error type of the scheme.
    type Error;

    /// [`CPSNARK::generate_keys`] generates the proving and verifying keys for
    /// `relation`, given one commitment key per external commitment.
    fn generate_keys(
        relation: Self::Relation,
        commitment_key: &[impl Borrow<Self::CommitmentKey> + Sync],
        rng: impl RngCore,
    ) -> Result<(Self::ProverKey, Self::VerifierKey), Self::Error>;

    /// [`CPSNARK::prove`] proves that `(x, w)` satisfies the relation and that
    /// the committed part of `w` is the message of the external commitments
    /// with openings `o` (one per commitment).
    fn prove(
        pk: &Self::ProverKey,
        x: &[Self::Field],
        w: &[Self::Field],
        o: &[Self::CommitmentOpening],
        rng: impl RngCore,
    ) -> Result<Self::Proof, Self::Error>;

    /// [`CPSNARK::verify`] verifies `proof` against the public inputs `x` and
    /// the external commitments `c`.
    fn verify(
        vk: &Self::VerifierKey,
        x: &[Self::Field],
        c: &[Self::Commitment],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error>;
}
