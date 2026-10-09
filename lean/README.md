# Lean 4 formalization of sonobe-v2

Build: `lake build` (Lean v4.30.0, Mathlib pinned to `c5ea0035`). No `sorry`; every theorem depends only
on `propext`, `Classical.choice`, `Quot.sound`. Cryptographic and trust assumptions are explicit
hypotheses of the theorems that use them, never axioms.

## Headline result

`Gadget.ivc_sound_of_circuits` (`FinalSoundness.lean`): an accepted `(n+1)`-step Nova + CycleFold IVC
proof certifies `z_{n+1} = F^{n+1}(z₀)`, where the statements `AugSound` / `CFSound` — *what a satisfying
assignment of the augmented / CycleFold circuit means* — are **derived from constraint-level models of
the Rust gadgets** (`Circuit/*`), not assumed. The decider (`IVC2/Decider.lean`) reduces to the same
statement.

## Layers

### Protocol level
| Module | Rust | Proved |
|---|---|---|
| `Commitment/Pedersen` | `commitments/pedersen.rs` | homomorphism, binding ⇐ no DL relation |
| `Arith/R1CS`, `Nova/Fold` | `arithmetizations/r1cs`, `nova/algorithms` | `fold_complete` |
| `Nova/Soundness` | | `fold_sound`: 3 distinct challenges ⇒ witnesses for `U` and `u` |
| `Nova/Transcript` | `Absorbable` impls | the Fiat–Shamir input determines `U`, `u`, `cm_t` |
| `Transcript/{Griffin,Sponge}` | `griffin/*` | gadget constraints pin the output to `permute`; duplex sponge; circuit sponge = spec sponge |
| `Snark/{LinearSubspace,LegoGroth16}` | `linear_subspace`, `cp/legogroth16` | completeness of the Groth16 check and the link |
| `IVC2/{Model,Soundness,Decider}` | `cyclefold/{mod,circuits}.rs` | **`ivc_sound`**, `decider_sound` — coordinate-level model |
| `IVC/*`, `Decider` | | earlier abstract model (`ivc_complete`); superseded for soundness by `IVC2` |

### Circuit level (`Circuit/*`) — constraint-by-constraint models, file:line of the Rust in the comments
| Module | Gadget | Result |
|---|---|---|
| `Basic`, `Bits` | `Boolean`, `is_zero`, `select`, `to_n_bits_le`, canonical `to_bits_le` | spec; unique binary expansion |
| `EC/{Affine,RCB,Projective,Convert}` | incomplete add/double; **Renes–Costello–Batina complete addition**; `to_affine`; `negate` | = group law on all valid projective points |
| `EC/{ScalarMul,ScalarMulSpec}`, `MulAdd` | `scalar_mul_le` (double-and-add) | = `ρ·P`, no exceptional case (needs `r > 2^n`) |
| `CycleFold`, `Coords`, `CFBridge` | `verify_point_rlc` | `R = P₀ + ρ·P₁`; **`CFSound` derived** |
| `Emulated/{Lt,Alloc,Carry,Canon,Absorb}` | `enforce_lt`, `Tight` alloc, carry chain of `enforce_equal_unaligned`, absorb | canonical limbs; integer lifting; absorbed pair `[V mod 2^253, V / 2^253]` |
| `FS2` | `FS2::Gadget::verify` | secondary fold = `foldInstance` (modulo arithmetic: `EmuArith`) |
| `Hash`, `Augmented`, `AugSound` | `compute_next_state` | **`AugSound` derived** |

## Rust change made on the way
`EnforceValid` (`primitives/src/algebra/group/mod.rs`, commit `b84a16a`): ark-r1cs-std's on-curve check
`Z(Y²−bZ²) = X(X²+aZ²)` is also satisfied by `(0,0,0)`, which the complete addition maps to `(0,0,0)` and
`to_affine` publishes as `(0,0)` = identity. A prover could present `P₀ + ρ·P₁` as the identity whenever `P₀`
is. The fix forbids `y = z = 0` on CycleFold witness points and on running/incoming instance commitments.
The Lean `CycleFold` model is of the fixed circuit.

## Findings that shaped the model
* The augmented circuit allocates primary commitments as `EmulatedAffineVar` (range-checked, **no curve
  check**) and `cm_e'`, `cm_w'` of the folded instance are *free* witnesses bound only through the
  CycleFold public inputs. Hence the coordinate-level model `IVC2`; `CFSound` lifts raw coordinates to
  genuine group elements.
* `pp_hash` is a free witness of the augmented circuit; the verifier's hash binds it (`HsInj`).
* Vectors are absorbed without a length prefix; the shape is fixed by `pp_hash`.
* The EVM contract does not check that commitment coordinates are canonical field elements/curve points.
* `modulo` of the emulated field: the static `Bounds` of the quotient (≤ 5) differ from the enforced range
  (32 bits). `u + ρ` is still sound (the top-limb equation forces `q ≲ 10`) but needs an
  operation-specific argument.

## Assumptions (explicit hypotheses of `ivc_sound_of_circuits`)
* `Circuit.Compiles`-direction `R1CS satisfied ⇒ constraint model` (arkworks synthesis); the models
  `AugRel` / `CFRel` are audited against the Rust code by hand.
* **`EmuArith`**: soundness of the emulated `modulo` arithmetic (`u+ρ`, `x·ρ+x`) — canonical allocation,
  `enforce_lt` and carry lifting are proved (`Circuit/Emulated`), the operation-specific static-bound
  argument is the one remaining emulated-field assumption.
* `HsInj` (collision resistance of the state hash incl. `pp_hash`), `¬DLRel` (binding), `Fork1/2`
  (rewinding / forking lemma), `CastOK`, `cpSound` (LegoGroth16 knowledge soundness, decider only).
* Curve facts: prime group order `r > 2^128`, no 2-torsion, `b ≠ 0`; field-size inequalities.
* Not derived from circuits: completeness of the augmented/CycleFold circuits (`AugComplete`,
  `CFComplete` in `IVC`), the step circuit (`StepRel`), and the secondary-fold challenge derivation
  (not needed for soundness: the model only uses that it is a 128-bit boolean string).
