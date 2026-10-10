# Lean 4 formalization of sonobe-v2

Build: `lake build` (Lean v4.30.0, Mathlib pinned to `c5ea0035`). No `sorry`; every theorem depends only
on `propext`, `Classical.choice`, `Quot.sound`. Cryptographic and trust assumptions are explicit
hypotheses of the theorems that use them, never axioms.

## Headline result

`Gadget.ivc_sound_of_circuits` (`FinalSoundness.lean`): an accepted `(n+1)`-step Nova + CycleFold IVC
proof certifies `z_{n+1} = F^{n+1}(z₀)`, where the statements `AugSound` / `CFSound` — *what a satisfying
assignment of the augmented / CycleFold circuit means* — are **derived from constraint-level models of
the Rust gadgets** (`Circuit/*`), not assumed.

`Gadget.ivc_complete_of_circuits` (`FinalCompleteness.lean`): the converse — an honest prover's IVC proof
is accepted — with `AugComplete` and `CFComplete` **derived** from the same circuit models
(`Circuit/{CFComplete,AugComplete,FS2Complete}`, `Circuit/Emulated/Complete`, `EC/ScalarMulComplete`).

`Gadget.evm_decider_sound` (`FinalDecider.lean`): if the generated **EVM contract** accepts a call
`(i, z₀, zᵢ, challenge, U.cm_e, U.cm_w, u.cm_w, cm_t, proof)` then `zᵢ = F^i(z₀)`. The decider circuit
(`Circuit/Decider`) and the contract (`EVM/Decider`) are modelled, so the former hypothesis `cpSound`
is gone; the only assumption on the CP-SNARK is `LegoGroth16.CPKnowledgeSound`.

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
| `IVC/{Model,Soundness,Completeness,Decider}` | `cyclefold/{mod,circuits}.rs` | **`ivc_sound`**, **`ivc_complete`** (given `AugComplete`, `CFComplete`), `decider_rel_{sound,complete}` — coordinate-level model |

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
| `EC/ScalarMulSpec` (`scalar_mul254_sound`) | `scalar_mul_le`, 254-bit scalars (252 affine bits + 2 complete-addition steps) | = `ρ·P` |
| `Decider/PedersenOpen` | `PedersenGadget<C2,true>::open` (msm, constant generators, `enforce_equal`) | cm = Pedersen commitment of the emulated limbs (`open_sound`) |
| `Decider/Primary` | `CycleFoldBasedIVCDeciderCircuit::generate_constraints` | `dec_sound`: `i ≠ 0`, `u_x`, challenge, packed public points, relaxed R1CS of `UU`, secondary relaxed R1CS + openings |
| `Snark/CPSound` | `LegoGroth16::verify` | `Accepts`, `CPKnowledgeSound` |
| `EVM/Decider` | `cyclefold_based_ivc_decider.sol`, `legogroth16.sol` | precompiles as partial functions, `DeciderAccepts`; `old_accepts_retarget` (pre-fix contract) |
| `FinalDecider` | | **`evm_decider_sound`** |

## Rust change made on the way
`EnforceValid` (`primitives/src/algebra/group/mod.rs`, commit `b84a16a`): ark-r1cs-std's on-curve check
`Z(Y²−bZ²) = X(X²+aZ²)` is also satisfied by `(0,0,0)`, which the complete addition maps to `(0,0,0)` and
`to_affine` publishes as `(0,0)` = identity. A prover could present `P₀ + ρ·P₁` as the identity whenever `P₀`
is. The fix forbids `y = z = 0` on CycleFold witness points and on running/incoming instance commitments.
The Lean `CycleFold` model is of the fixed circuit.

## Second Rust change: bind the decider's points to the circuit
Commit `5097342`. The decider circuit did not tie the verifier's folded commitments to its own `U`, `u`,
`π`: the calldata points `U.cm_e, U.cm_w, u.cm_w, cm_t` were never inputs of the circuit, and since the
relaxed-R1CS slack `e` is free, a prover could pick `U.cm_e := c − ρ·cm_t` after the fact
(`EVM.old_accepts_retarget` formalises this freedom; the native verifier needed ≈2^128 grinding because
`U` enters the hash). The circuit now exposes those four points as public inputs, **packed** (two field
elements per coordinate, `[V mod 2^253, V >> 253]`, the same encoding as `Absorbable`), which keeps the
number of public inputs below the previous one (24 instead of 32 for the points), and the verifier folds
them with the circuit's own challenge. `LegoGroth16::verify` also rejects wrongly sized inputs.

## Findings that shaped the model
* The augmented circuit allocates primary commitments as `EmulatedAffineVar` (range-checked, **no curve
  check**) and `cm_e'`, `cm_w'` of the folded instance are *free* witnesses bound only through the
  CycleFold public inputs. Hence the coordinate-level model `IVC`; `CFSound` lifts raw coordinates to
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
* **`EmuR1CS`** (`Circuit/Decider/Primary`): the emulated-field relaxed R1CS check of the CycleFold
  instance (`evaluate_r1cs` + `enforce_equivalent` over `EmulatedFieldVar`) is sound for canonical inputs —
  the decider's counterpart of `EmuArith`.
* **`LegoGroth16.CPKnowledgeSound`** (decider only): an accepted LegoGroth16 proof yields a satisfying
  assignment of the decider R1CS whose committed blocks (`WW.e`, `WW.w`) open the commitments. Also
  trusted: the order of committed variables (`CommittedCache`, `pedersen.rs:435`), the decode of
  precompile inputs (`EVM.decodeG1`), and that constants (`dk2`) satisfy the scalar-mul chain relations
  they are computed from.
* `HsInj` (collision resistance of the state hash incl. `pp_hash`), `¬DLRel` (binding), `Fork1/2`
  (rewinding / forking lemma), `CastOK`.
* Curve facts: prime group order `r > 2^128`, no 2-torsion, `b ≠ 0`; field-size inequalities.
* Completeness side (`ivc_complete_of_circuits`) additionally trusts: `EmuArith.Complete` (the emulated
  `modulo` arithmetic has witnesses), the completeness direction of the R1CS synthesis
  (`AugRel ⇒ ∃ w, Sat`), and that the step circuit is satisfiable (`StepRel z (step z)`).
* Not modelled: the step circuit itself (`StepRel` is abstract). The Fiat–Shamir derivation of the
  secondary challenges is part of `AugRel` (`ChalRel`) and is used by the completeness proof.
