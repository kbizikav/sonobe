# Lean 4 formalization of sonobe-v2

Build: `lake build` (Lean v4.30.0, Mathlib pinned to `c5ea0035`). No `sorry`; theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`. Every cryptographic or circuit assumption is an explicit
hypothesis of the theorem that uses it, never an axiom.

## Layers

### 1. Protocol level (`Commitment`, `Arith`, `Nova`, `Transcript`, `Snark`, `IVC`, `IVC2`, `Decider`)
| Module | Rust | Proved |
|---|---|---|
| `Commitment/Pedersen` | `commitments/pedersen.rs` | homomorphism, binding ⇐ no DL relation |
| `Arith/R1CS`, `Nova/Fold` | `arithmetizations/r1cs`, `nova/algorithms` | `fold_complete` |
| `Nova/Soundness` | | `fold_sound`: 3 distinct challenges ⇒ witnesses for `U` and `u` |
| `Nova/Transcript` | `Absorbable` impls | the Fiat-Shamir input determines `U`, `u`, `cm_t` |
| `Transcript/Griffin`, `Sponge` | `griffin/*` | gadget constraints pin the output to `permute`; duplex sponge; circuit sponge = spec sponge |
| `Snark/LinearSubspace`, `LegoGroth16` | `linear_subspace`, `cp/legogroth16` | completeness (Groth16 check and link) |
| `IVC` (+`Completeness`) | `cyclefold/{mod,circuits}.rs` | `ivc_complete`; abstract-model soundness |
| `IVC2` | | **`IVC2.ivc_sound`** — coordinate-level model (see below) |
| `Decider` | `cyclefold/mod.rs:480+` | `decider_rel_complete`, `decider_sound` (abstract model) |

### 2. Circuit level (`Circuit/*`) — constraint-by-constraint models of the Rust gadgets
Each gadget is a conjunction of field equations; soundness (`rel ⇒ spec`) is proved against the
ark-r1cs-std / sonobe code (file:line in the doc comments).
| Module | Gadget | Result |
|---|---|---|
| `Circuit/Basic` | `Boolean`, `is_zero`, `select`, `conditional_enforce_equal` | spec of each |
| `Circuit/Bits` | `to_n_bits_le`, canonical `to_bits_le` (`enforce_in_field_le`) | unique binary expansion |
| `Circuit/EC/Affine` | `NonZeroAffineVar::{add_unchecked, double}` | = group law |
| `Circuit/EC/RCB`, `Projective` | complete addition (Renes–Costello–Batina Alg. 1) | **= group law on all valid projective points** |
| `Circuit/EC/Convert` | `to_affine`, `negate` | spec |
| `Circuit/EC/ScalarMul`, `ScalarMulSpec` | `scalar_mul_le` (double-and-add chain) | = `ρ · P`, **no exceptional case** (needs group order `r > 2^n`) |
| `Circuit/CycleFold` | `NovaCycleFoldCircuit::verify_point_rlc` | `R = P₀ + ρ·P₁` |
| `Circuit/CFBridge` | | **`Setup2.CFSound` derived** from the circuit constraints |
| `Circuit/Emulated/{Lt,Alloc,Carry,Absorb}` | `enforce_lt`, `Tight` allocation, `enforce_equal_unaligned`, absorb | canonical limbs; carry chain integer lifting; absorbed pair = `[V mod 2^253, V / 2^253]` |

## Rust change made on the way
`EnforceValid` (`primitives/src/algebra/group/mod.rs`): ark-r1cs-std's on-curve check
`Z(Y²−bZ²) = X(X²+aZ²)` is also satisfied by `(0,0,0)`, which the complete addition maps to `(0,0,0)`
and `to_affine` publishes as `(0,0)` = identity. A prover could thus present `P₀ + ρ·P₁` as the identity
whenever `P₀` is. The fix forbids `y = z = 0` on CycleFold witness points and on the commitments of
running/incoming instance variables. The Lean model of `CycleFold` is of the fixed circuit.

## Findings that shaped the model
* The augmented circuit allocates primary commitments as `EmulatedAffineVar` (range-checked, **no
  curve check**), and `cm_e'`, `cm_w'` of the folded instance are *free* witnesses tied to the fold only
  through the CycleFold public inputs. Hence `IVC2` works with raw coordinate pairs, and `CFSound` lifts
  them to genuine group elements.
* The public-parameter hash `pp_hash` is a free witness of the augmented circuit; the verifier's hash
  binds it (`IVC2.Setup2.HsInj`).
* Vectors are absorbed without a length prefix; shape is fixed by `pp_hash`.
* The contract does not check that commitment coordinates are canonical field elements/curve points.
* `modulo` of the emulated field: static `Bounds` of the quotient (≤ 5) differ from the enforced range
  (32 bits). Soundness still holds for `u + ρ` because the top-limb equation forces `q ≲ 10`, but it needs
  an operation-specific argument — kept as the single hypothesis `EmuArith` (to do).

## Assumptions still explicit (hypotheses)
`AugSound` (to be derived from `Circuit/*`), `HsInj` (hash collision resistance incl. `pp_hash`),
`¬DLRel` (binding), `Fork1/2` (rewinding / forking lemma), `CastOK`, `Circuit.Compiles` (arkworks
R1CS synthesis), curve facts (prime order `r > 2^128`, no 2-torsion, `b ≠ 0`), `EmuArith`.
