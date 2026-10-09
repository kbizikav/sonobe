# Lean 4 formalization of sonobe-v2

Build: `lake build` (Lean v4.30.0, Mathlib pinned to `c5ea0035`). No `sorry`; theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`. All cryptographic/circuit assumptions are explicit
hypotheses of the theorems, not axioms.

| Module | Rust | Proved |
|---|---|---|
| `Commitment/Pedersen` | `commitments/pedersen.rs` | homomorphism, `commit_fold`, binding ⇐ no DL relation |
| `Arith/R1CS` | `arithmetizations/r1cs` | relaxed R1CS, quadratic expansion `eval_fold` |
| `Nova/Fold` | `nova/algorithms` | `fold_complete` |
| `Nova/Soundness` | | `fold_sound`: 3 distinct challenges ⇒ witnesses for `U` and `u` (interpolation + binding) |
| `Nova/Transcript` | `Absorbable` impls | the Fiat-Shamir input determines `U`, `u`, `cm_t` (injective) |
| `Transcript/Griffin` | `griffin/mod.rs` | `permRel_iff`: the gadget constraints pin the output to `permute` |
| `Transcript/Sponge` | `griffin/sponge.rs` | duplex state machine, `add_append`, `circuit_sponge_bind` |
| `IVC/Model`, `Completeness` | `cyclefold/{mod,circuits}.rs` | `ivc_complete` |
| `IVC/Soundness` | | `ivc_sound`: accepted n-step proof ⇒ `zₙ = Fⁿ(z₀)` |
| `Snark/LinearSubspace` | `linear_subspace` | completeness, `verify_eq`, generic-group row extraction |
| `Snark/LegoGroth16` | `cp/legogroth16` | `groth16_complete` (scalar identity + pairing), `lego_complete` (with link) |
| `Decider` | `cyclefold/mod.rs:480+` | `decider_rel_complete`, `decider_sound` |

## Assumptions made explicit (hypotheses)
* `AugSound`/`AugComplete`, `CFSound`/`CFComplete`: meaning of satisfying assignments of the augmented
  and CycleFold circuits. **Not yet derived from constraints** (next step: gadget-level R1CS models for
  EC addition, bit decomposition, Nova partial verifier, using `Griffin.permRel_iff` for the sponge).
* `HsInj`: collision resistance / injective encoding of `H(i, z₀, zᵢ, U, cf_U)`.
* `¬ DLRel` for the four commitment keys (binding).
* `Fork1`/`Fork2`: rewinding (forking lemma) — accepting folds can be re-run on 3 distinct challenges.
* `cpSound`: LegoGroth16 knowledge soundness (generic-group), incl. public-input encoding.

## Findings from the Rust code that shape the model
* Vectors are absorbed without a length prefix; `chalInput_injective` needs the shape fixed (pp_hash).
* The new commitments of `UU` are free witnesses of the augmented circuit; they are bound only through
  the CycleFold public inputs (`AugSound` + `CFSound` ⇒ `pe = U.cmE + ρ·π`).
* The contract does not check that commitment coordinates are canonical field elements/curve points.
