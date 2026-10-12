//! Solidity codegen traits and templates for the on-chain decider verifier.

use ark_bn254::Bn254;
use ark_std::{borrow::Borrow, marker::PhantomData};
use askama::Template;
use sonobe_fs::{Error, FoldingSchemeVerifier};
use sonobe_primitives::circuits::FCircuit;
use sonobe_snarks::cp::legogroth16::VerifierKey;

/// [`DeciderFoldFragment`] is the Solidity code emitted by a folding scheme for
/// the decider verifier contract, which folds the running and incoming
/// instances' commitments on-chain (the point RLC left as hints by the decider
/// circuit).
pub struct DeciderFoldFragment {
    /// [`DeciderFoldFragment::challenge`] is the name of the `uint256`
    /// parameter that carries the folding challenge.
    pub challenge: String,
    /// [`DeciderFoldFragment::params`] are the Solidity parameter declarations
    /// of the instances' and the folding proof's commitments, in the order of
    /// the calldata produced by [`FoldingSchemeEVMExt::verify_calldata`].
    pub params: Vec<String>,
    /// [`DeciderFoldFragment::body`] is the Solidity code that computes the
    /// folded commitments from [`DeciderFoldFragment::params`] and the
    /// challenge.
    pub body: String,
    /// [`DeciderFoldFragment::commitments`] are the names of the folded
    /// commitments computed in [`DeciderFoldFragment::body`], in the order of
    /// the folded running instance's `commitments()`.
    pub commitments: Vec<String>,
    /// Names of the `uint256[2]` parameters that are public inputs of the
    /// decider circuit, in circuit order: the points the fold works with.
    pub public_points: Vec<String>,
}

/// [`FoldingSchemeEVMExt`] extends a folding scheme with what the on-chain
/// decider verifier needs from it.
pub trait FoldingSchemeEVMExt<const M: usize, const N: usize>: FoldingSchemeVerifier<M, N> {
    /// [`FoldingSchemeEVMExt::decider_fold_fragment`] returns the Solidity
    /// fragment that folds the commitments on-chain.
    fn decider_fold_fragment() -> DeciderFoldFragment;

    /// [`FoldingSchemeEVMExt::verify_calldata`] serializes the commitments of
    /// the running instances `Us`, the incoming instances `us` and the folding
    /// `proof` into calldata matching [`DeciderFoldFragment::params`].
    #[allow(non_snake_case)]
    fn verify_calldata(
        Us: &[impl Borrow<Self::RU>; M],
        us: &[impl Borrow<Self::IU>; N],
        proof: &Self::Proof<M, N>,
    ) -> Result<Vec<u8>, Error>;
}

/// [`DeciderStateFragment`] is the Solidity code emitted by a step circuit for
/// handling its state in the decider verifier contract.
pub struct DeciderStateFragment {
    /// [`DeciderStateFragment::type_name`] is the Solidity type of the state
    /// parameters `z_0` and `z_i`.
    pub type_name: String,
    /// [`DeciderStateFragment::type_def`] is the definition of a custom
    /// Solidity type used by [`DeciderStateFragment::type_name`], if any
    /// (empty otherwise).
    pub type_def: String,
    /// [`DeciderStateFragment::shape_check_body`] is the body of
    /// `_checkStateShape(z)`, which reverts if `z` does not have the shape of
    /// the reference state (see [`FCircuit::same_state_shape`]).
    pub shape_check_body: String,
    /// [`DeciderStateFragment::flatten_body`] is the body of
    /// `_flattenState(z)`, which returns the state as the flat `uint256` array
    /// of field elements the decider circuit takes as public inputs.
    pub flatten_body: String,
}

/// [`FCircuitEVMExt`] extends a step circuit with what the on-chain decider
/// verifier needs from it.
pub trait FCircuitEVMExt: FCircuit {
    /// [`FCircuitEVMExt::decider_state_fragment`] returns the Solidity fragment
    /// handling states shaped like `reference`.
    fn decider_state_fragment(reference: &Self::State) -> DeciderStateFragment;
}

/// [`CycleFoldBasedIVCDeciderVerifierTemplate`] is rendered as the contract
/// `DeciderVerifier` via [`askama`].
#[derive(Template)]
#[template(path = "cyclefold_based_ivc_decider.sol.askama")]
pub struct CycleFoldBasedIVCDeciderVerifierTemplate<
    'a,
    FS: FoldingSchemeEVMExt<1, 1>,
    FC: FCircuitEVMExt,
> {
    _t: PhantomData<FS>,
    vk: &'a VerifierKey<Bn254>,
    reference_state: &'a FC::State,
}

impl<'a, FS: FoldingSchemeEVMExt<1, 1>, FC: FCircuitEVMExt>
    CycleFoldBasedIVCDeciderVerifierTemplate<'a, FS, FC>
{
    /// [`CycleFoldBasedIVCDeciderVerifierTemplate::new`] creates the template
    /// from the decider's LegoGroth16 verifier key `vk` and the reference state
    /// `reference_state` that fixes the state shape.
    pub fn new(vk: &'a VerifierKey<Bn254>, reference_state: &'a FC::State) -> Self {
        Self {
            _t: PhantomData,
            vk,
            reference_state,
        }
    }
}
