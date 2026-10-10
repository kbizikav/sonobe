# Findings in the Rust implementation

Written for the sonobe maintainers. These issues were found while formalizing the Nova + CycleFold
IVC and its decider in Lean (`lean/`): a proof cannot be completed unless the circuit actually
enforces what the statement needs, so the places where it could not be completed pointed at
missing constraints. This is **not a full audit**; it lists what the formalization surfaced.

All items are fixed on branch `lean-formalization` (commits below). Each fix was checked with
`cargo test` (release, `--features evm`).

| # | Issue | Severity | Fixed in |
|---|---|---|---|
| F1 | The decider's public inputs do not bind the circuit's `U`, `u`, `π` to the commitments the EVM contract folds | **Critical** (EVM verifier) | `5097342` |
| F2 | `(0,0,0)` passes the on-curve check of `ProjectiveVar`, so the CycleFold relation can be falsified when a commitment is the identity | **High** (IVC soundness) | `b84a16a` |
| F3 | Loosely allocated emulated integers can exceed their static bounds in the top limb | Medium, exploitability not established | `beea230` |
| F4 | `LegoGroth16::verify` silently ignores surplus / missing public inputs (`zip`) | Low–Medium | `5097342` |
| F5 | Pedersen gadgets: silent truncation of `msm`; implicit ordering contract of committed variables | Low (hardening) | `9a4b0d1` |

---

## F1. Decider: the contract's points are not tied to the circuit (Critical for the EVM verifier)

**What was wrong.** `CycleFoldBasedIVCDeciderCircuit` folds the incoming instance `u` into the
running instance `U` *inside* the circuit, but leaves the folded commitments `UU.cm_e`, `UU.cm_w`
as free hints. Its public inputs were `[i, z_0, z_i, challenges, UU.cm_e, UU.cm_w]`. The four points
that the verifier folds — `U.cm_e`, `U.cm_w`, `u.cm_w`, `cm_t` — were **not** inputs of the circuit,
so nothing related them to the circuit's own `U`, `u` and proof. The generated contract
(`cyclefold_based_ivc_decider.sol`) takes these points and `challenge` from calldata and only
computes `cm_e = U_cm_e + ρ·cm_t`, `cm_w = U_cm_w + ρ·u_cm_w` with `ρ = challenge & (2^128-1)`.

**Why it matters.** For any claimed `(i, z_0, z_i)`, including false ones:

1. The prover picks any `U`, `u`, `π` (witnesses) and computes `ρ` as the circuit does. The relaxed
   R1CS slack `e` is a free witness, so the check of `UU` is satisfied with `w = 0` and `e :=` the
   evaluation, and `cm_e, cm_w` are then the Pedersen commitments to `e` and `0`.
2. The prover chooses the calldata points *after the fact*: `U_cm_e := cm_e − ρ·cm_t`,
   `U_cm_w := cm_w − ρ·u_cm_w`. The contract recomputes exactly `cm_e, cm_w` and accepts.
3. The secondary (CycleFold) side is satisfied by the trivial zero instance, and `u.x = H(i, z_0,
   z_i, U, cf_U)` is a free witness equal to that hash by construction.

So a valid LegoGroth16 proof is obtained for a *false* statement without breaking any assumption:
**the EVM verifier would accept arbitrary claims `z_i = F^i(z_0)`.** The native Rust verifier is not
affected in practice, because it recomputes `ρ` from a transcript that contains `U`, which makes the
choice in step 2 circular (≈ 2^128 work).

*Status of the evidence:* the reasoning was derived from the circuit and contract code and is
formalized in Lean (`EVM.old_accepts_retarget`: the pre-fix contract's acceptance depends only on the
folded commitments, so the four points can be re-chosen freely). We did **not** run an end-to-end
exploit against a deployed contract.

**Fix.** The four points are now public inputs of the decider circuit, packed as two field elements per
coordinate (`[V mod 2^253, V >> 253]`, the same encoding as `Absorbable`), so the verifier folds
*the circuit's* points with *the circuit's* challenge. `UU.cm_*` use the same packing. The number of
point-related public inputs goes from 32 to 24, so verification gas decreases:
**669,386 → 603,668** on the repository's test circuit (`test_nova_nova_decider_evm`).
Tests: tampering with any calldata word, the challenge, or the input count is rejected.

## F2. `(0,0,0)` passes the on-curve check (High)

**What was wrong.** ark-r1cs-std's `ProjectiveVar` on-curve constraint is
`Z·(Y² − b·Z²) = X·(X² + a·Z²)`, which is also satisfied by `(0,0,0)`. A witness point allocated
with `new_witness` can therefore be `(0,0,0)`. The complete addition (Renes–Costello–Batina) maps any
sum involving `(0,0,0)` to `(0,0,0)`, and `to_affine` publishes it as `(0,0)`, the encoding of the
identity.

**Why it matters.** In the CycleFold circuit (`verify_point_rlc`) a prover may allocate `P₀ = (0,0,0)`
whenever the genuine `P₀` is the identity. The circuit then publishes `R = P₀ + ρ·P₁` as the
identity for **any** `P₁` and `ρ`, i.e. it "proves" `R = 0` instead of `R = ρ·P₁`. The folded
primary commitment `UU.cm_e` / `UU.cm_w` is bound only through these CycleFold public inputs, so it can
be forced to the identity instead of `U.cm + ρ·(proof / u.cm_w)`.

The precondition is that a running commitment is the identity. This holds for the **dummy running
instance of the base case (all commitments are zero), i.e. at the first step after the base case**.
Dropping the incoming commitment from the fold would let a prover skip the check that the previous
step's instance is satisfiable. We did not construct a complete forgery of a state transition; the
issue is that the folding relation the soundness argument relies on is not enforced.

*Evidence:* `test_zero_triple_passes_on_curve_check` reproduces that the on-curve constraint accepts
`(0,0,0)`.

**Fix.** New trait `EnforceValid` (`y = 0 ∧ z = 0` is rejected via `Boolean::enforce_kary_nand`),
applied to all witness points of the CycleFold circuit and to the commitments of running/incoming
instances. It is a no-op for emulated affine points (which already encode the identity as `(0,0)`
without a projective ambiguity).

## F3. Loose emulated allocation: top limb exceeds its static bound (Medium)

**What was wrong.** `LimbedVar::alloc` with `RangeCheckMode::Loose` enforces `BITS_PER_LIMB` (32) bits
on *every* limb, but the static `Bounds` were derived from the declared bit length. For lengths not
divisible by 32 the top limb could hold up to `2^32−1` while the bounds claimed `2^(len mod 32)`
(example: declared 40 bits, accepted top limb `2^19`; test `test_loose_alloc_top_limb_range`).
Loose allocation is used for the quotient `q` in `modulo` and `enforce_congruent`, whose bounds feed
the no-overflow analysis of `mul_unaligned` / `enforce_equal_unaligned`.

**Why it matters / status.** A value outside the static bound can make a group sum in
`enforce_equal_unaligned` exceed the safe window and wrap modulo the native prime, which would
invalidate the carry argument. **We did not find a concrete exploit** and do not claim one; the
margins depend on the actual bound geometry. The fix removes the possibility.

**Fix.** In loose mode the length is rounded up to whole limbs, so the bounds match the constraints.
All existing tests, including the decider tests, still pass (the circuit shape, hence the keys,
changes slightly).

## F4. `LegoGroth16::verify` ignores mismatched input lengths (Low–Medium)

`verify` combined the public inputs with `gamma_abc_g1_pub` using `zip`, which silently drops the
longer side: surplus inputs were ignored and missing inputs contributed nothing. A proof for `x` is
then accepted for `x ++ extra`, and a shorter `x` is verified as if the missing inputs were absent.
It does not forge a false statement at a fixed interface, but it breaks the expectation that
`verify` binds the whole statement. The Solidity verifier is unaffected (fixed-size arrays).

**Fix.** `verify` rejects inputs and commitments whose lengths differ from the verification key's.

## F5. Pedersen gadgets: hardening (Low)

* `PedersenGadget::msm` zipped generators with scalars, silently dropping scalars if the key were
  shorter (the native `commit` already returns `MessageTooLong`). Not reachable today because
  `generate_keys` checks the key length, but the circuit did not check it.
* `PedersenCommitAndProveGadget::open` relies on an unstated contract with `LegoGroth16`: the
  committed variables must be in ascending index order across `open` calls (the key blocks are paired
  with the committed variables in that order). It holds today because the running witness is allocated
  as `e` before `w` and opened in that order; reordering either would silently mislink a commitment
  (see the `TODO` in `pedersen.rs`).

**Fix.** Both are now checked and fail at setup (`Unsatisfiable`) instead of silently misbehaving.

---

## Observations (no change made)

* The augmented circuit allocates `pp_hash` as a free witness. This is sound only because the
  verifier recomputes the final hash with its own `pp_hash`; the decider uses a constant.
* `verifyProof` of the generated contract is `public` (inherited); only `verifyDeciderProof` has the
  guarantees above.
* The contract's `rho = challenge & ((1 << CHALLENGE_BITS) - 1)` equals the circuit's challenge only for
  the circuit's `CHALLENGE_BITS` (128 by default).
* Vectors are absorbed without a length prefix; shapes are fixed by `pp_hash`/the key, but the
  state-shape check (`same_state_shape`) lives outside the circuit.
* Emulated `modulo`: the static quotient bounds and the enforced range differ; we could not close this
  with a proof and keep it as an explicit assumption (`EmuArith`, see `README.md`).
