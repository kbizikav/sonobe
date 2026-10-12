#![warn(missing_docs)]

//! This crate provides the SNARKs used by Sonobe to compress IVC proofs.
//!
//! It includes the commit-and-prove SNARK abstraction [`cp::CPSNARK`] with its
//! LegoGroth16 instantiation [`cp::legogroth16::LegoGroth16`], and the linear
//! subspace SNARK [`linear_subspace::LinearSubspaceSNARK`] that LegoGroth16
//! uses to link its internal witness commitment to external commitments.

pub mod cp;
pub mod linear_subspace;
