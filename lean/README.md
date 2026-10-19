# Lean 4 formalization of sonobe-v2

Formalizes the Nova + CycleFold IVC, Pedersen commitments, the Poseidon transcript, the LegoGroth16
decider and its EVM verifier, **down to the R1CS gadgets** (Lean + Mathlib, `lake build`, no `sorry`;
every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`).

## Main results

The step is a relation `StepRel z w z'`, the step circuit's constraints with `w` its wires (external
inputs included), and `Chain StepRel z₀ ws zₙ` says that `ws` takes `z₀` to `zₙ` one step per
witness.

| Theorem (file) | Meaning |
|---|---|
| `ivc_sound_of_circuits` (`FinalSoundness`) | An accepted `(n+1)`-step IVC proof, whose run meets `RunOK`, gives `ws` of length `n+1` with `Chain StepRel z₀ ws z_{n+1}`. |
| `ivc_complete_of_circuits` (`FinalCompleteness`) | For every `Chain StepRel z₀ ws zₙ`, an honest prover's proof of `(|ws|, z₀, zₙ)` is accepted. |
| `evm_decider_sound` (`FinalDecider`) | If the generated EVM contract accepts `(i, z₀, zᵢ, …)`, and the run meets its hypotheses (`ExtractsAt`, `ExtractionOK`), there are `ws` of length `i` with `Chain StepRel z₀ ws zᵢ`. |

What the circuits must satisfy is **derived** from constraint-level models of the Rust gadgets, not
assumed: bit decompositions, `to_affine`, complete addition, double-and-add, canonical emulated
limbs, `enforce_lt`, the emulated `modulo` / `enforce_congruent` / relaxed-R1CS check (`add_unaligned`,
`mul_unaligned`, the carry argument of `enforce_equal_unaligned`), absorb, the Poseidon sponge,
the Fiat–Shamir challenges, the fold verifiers, the decider circuit and the contract (with
precompiles as partial functions). The transcript is arkworks' `PoseidonSponge` with circomlib's
`Poseidon(4)` constants (`Poseidon.circom5`, zERC20's `POSEIDON4`): its permutation gadget is
equivalent to the permutation (`Poseidon.permRel_iff`), and arkworks' absorb/squeeze loops are the
sponge the proofs use, for any permutation (`SpongeCfg.absorb_eq_add`, `squeeze_eq_get`).

## What is assumed

* **Cryptography, per run.** Every cryptographic assumption is about the values of one run:
  * `ExtractsAt` — the CP-SNARK's knowledge soundness at the call: the witness its extractor
    outputs on the accepted call satisfies the decider's R1CS and opens the commitments;
  * `Rewind.Accepts` — rewinding each fold the run verified gives two more accepting witnesses at
    other challenges (the forking lemma);
  * `Rewind.Binds` — binding holds at the openings those witnesses give (`PedersenKey.BindsAt`); a
    break is a discrete-log relation computed from them (`PedersenKey.dlRel_of_not_bindsAt`);
  * `Setup.HashOK` — the state hash does not collide on the verifier's input and the circuit's at
    any step (`Setup.HsAt`).

  `ExtractionOK` (decider) and `RunOK` (IVC) collect them along the run. `Hypotheses.lean` checks
  in a group of prime order that each run hypothesis holds for an honest run and fails for a
  cheating one.
* **Emulated-field arithmetic**: only the completeness half, `EmuArith.Complete` (the honest
  prover can satisfy `modulo`). Soundness is derived; the theorems assume the synthesis of the
  carry plans succeeded (it is part of the relations `ModRel`/`CongRel`) and that the static bounds
  in `Emulated/{Bounds,Shapes}` match `emulated.rs` (checked for `u + ρ` and `b·ρ + a` by
  `diff/` and the Rust test `test_static_bounds_match_lean`; the R1CS row shapes are not covered). The statements take `bitsLen(p₂−1) = 254`.
* **Model fidelity** (audited by hand, plus an independent review of each module against the Rust
  code): that `AugRel`, `CFRel`, `DecRel` and the contract model are consequences of the Rust
  constraints, and for completeness that they are also sufficient (R1CS satisfiability); that the
  committed variables of the CP-SNARK are `WW.e` then `WW.w`; that the step circuit's constraints
  in the augmented circuit are `StepRel` on its wires, independent of `i`.
* **Math facts**: prime group orders above `2^128`/`2^252`, no 2-torsion, `b ≠ 0`, field-size
  inequalities.

Everything is an explicit hypothesis of the theorems that use it; there are no axioms.

## Layout

| Directory | Content |
|---|---|
| `Commitment`, `Arith`, `Nova`, `Transcript`, `Snark` | Protocol level: Pedersen, R1CS, Nova folding and its soundness (`Rewind`), the sponge and the Poseidon permutation, LinearSubspace / LegoGroth16 (+ `ExtractsAt`) |
| `IVC` | Coordinate-level IVC model: `Chain`, `ivc_sound`, `ivc_complete`, decider relation |
| `Circuit` | Constraint-level gadget models and their soundness/completeness: `Basic`, `Bits`, `EC`, `Emulated`, `Hash`, `FS2`, `CycleFold`, `Augmented`, `Decider` |
| `EVM` | The generated Solidity verifier at the level of 256-bit words |
| `Final*.lean` | The three headline theorems above |
| `Hypotheses.lean` | The run hypotheses in a non-degenerate model |

## Build

`lake build` (Lean `v4.30.0`, Mathlib pinned in `lake-manifest.json`).
