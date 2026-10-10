# Lean 4 formalization of sonobe-v2

Formalizes the Nova + CycleFold IVC, Pedersen commitments, Griffin transcript, the LegoGroth16
decider and its EVM verifier, **down to the R1CS gadgets** (Lean + Mathlib, `lake build`, no `sorry`;
every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`).

## Main results

| Theorem (file) | Meaning |
|---|---|
| `ivc_sound_of_circuits` (`FinalSoundness`) | An accepted `(n+1)`-step IVC proof certifies `z_{n+1} = F^{n+1}(z₀)`. |
| `ivc_complete_of_circuits` (`FinalCompleteness`) | An honest prover's proof is accepted. |
| `evm_decider_sound` (`FinalDecider`) | If the generated EVM contract accepts `(i, z₀, zᵢ, …)`, then `zᵢ = Fⁱ(z₀)`. |

What the circuits must satisfy is **derived** from constraint-level models of the Rust gadgets, not
assumed: bit decompositions, `to_affine`, complete addition, double-and-add, canonical emulated
limbs, `enforce_lt`, absorb, the Griffin sponge, the Fiat–Shamir challenges, the fold verifiers, the
decider circuit and the contract (with precompiles as partial functions).

## What is assumed

* **Cryptography**: collision resistance of the state hash, binding of the four Pedersen keys, the
  rewinding (forking) lemma `Fork1/2`, and `LegoGroth16.CPKnowledgeSound` (the only assumption on the
  CP-SNARK).
* **Emulated-field arithmetic**: `EmuArith`, `EmuR1CS` (soundness of `modulo`-based operations) and
  `EmuArith.Complete`.
* **Model fidelity** (audited by hand, plus an independent review of each module against the Rust
  code): that `AugRel`, `CFRel`, `DecRel` and the contract model are consequences of the Rust
  constraints, and for completeness that they are also sufficient (R1CS satisfiability); that the
  committed variables of the CP-SNARK are `WW.e` then `WW.w`; that the step circuit is satisfiable.
* **Math facts**: prime group orders above `2^128`/`2^252`, no 2-torsion, `b ≠ 0`, field-size
  inequalities.

Everything is an explicit hypothesis of the theorems that use it; there are no axioms.

## Layout

| Directory | Content |
|---|---|
| `Commitment`, `Arith`, `Nova`, `Transcript`, `Snark` | Protocol level: Pedersen, R1CS, Nova folding and its soundness, Griffin sponge, LinearSubspace / LegoGroth16 (+ `CPKnowledgeSound`) |
| `IVC` | Coordinate-level IVC model: `ivc_sound`, `ivc_complete`, decider relation |
| `Circuit` | Constraint-level gadget models and their soundness/completeness: `Basic`, `Bits`, `EC`, `Emulated`, `Hash`, `FS2`, `CycleFold`, `Augmented`, `Decider` |
| `EVM` | The generated Solidity verifier at the level of 256-bit words |
| `Final*.lean` | The three headline theorems above |

## Build

`lake build` (Lean `v4.30.0`, Mathlib pinned in `lake-manifest.json`).
