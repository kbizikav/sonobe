# Issues found in the Rust implementation

These issues came up while formalizing the Nova + CycleFold IVC and its decider in Lean: a proof
cannot be completed unless the circuit enforces what the statement needs, and the places where it
failed pointed at missing constraints. The list is what the formalization surfaced, not a full audit.
All items are fixed on this branch; `cargo test --release --features evm` passes.

| # | Issue | Severity | Fix |
|---|---|---|---|
| F1 | Decider public inputs do not bind the points the EVM contract folds | **Critical** (EVM verifier) | `5097342` |
| F2 | `(0,0,0)` passes the on-curve check, so the CycleFold relation can be falsified | **High** | `b84a16a` |
| F3 | Loosely allocated emulated integers can exceed their static bounds | Medium (no exploit shown) | `beea230` |
| F4 | `LegoGroth16::verify` ignores surplus or missing public inputs | Low–Medium | `5097342` |
| F5 | Pedersen gadgets: silent truncation in `msm`, implicit ordering of committed variables | Low | `9a4b0d1` |
| F6 | `enforce_equal_unaligned` does not guarantee the integer equality it is used for | Medium (no exploit shown) | `2a73249` |

## F1. The decider does not bind the points the contract folds

`CycleFoldBasedIVCDeciderCircuit` folds `u` into `U` inside the circuit but leaves the folded
commitments `UU.cm_e`, `UU.cm_w` as free hints. Its public inputs were
`[i, z_0, z_i, challenges, UU.cm_e, UU.cm_w]`; the four points the verifier folds (`U.cm_e`,
`U.cm_w`, `u.cm_w`, `cm_t`) were not inputs, so nothing related them to the circuit's own `U`, `u`
and proof. The generated contract takes these points and `challenge` from calldata and computes
`cm_e = U_cm_e + ρ·cm_t`, `cm_w = U_cm_w + ρ·u_cm_w` with `ρ = challenge & (2^128 - 1)`.

For any claimed `(i, z_0, z_i)`, including a false one:

1. The prover chooses arbitrary `U`, `u`, `π` and computes `ρ` as the circuit does. The relaxed R1CS
   slack `e` is a free witness, so the check of `UU` holds with `w = 0` and `e` equal to the
   evaluation; `cm_e`, `cm_w` are the Pedersen commitments to `e` and `0`.
2. The prover then picks the calldata points after the fact: `U_cm_e := cm_e − ρ·cm_t` and
   `U_cm_w := cm_w − ρ·u_cm_w`. The contract recomputes exactly `cm_e`, `cm_w` and accepts.
3. The CycleFold side is satisfied by the zero instance, and `u.x = H(i, z_0, z_i, U, cf_U)` is a
   free witness equal to that hash by construction.

The result is a valid LegoGroth16 proof of a false statement without breaking any cryptographic
assumption: **the EVM verifier would accept arbitrary claims `z_i = F^i(z_0)`.** The native verifier
recomputes `ρ` from a transcript that contains `U`, which makes step 2 circular (about 2^128 work).

This follows from reading the circuit and the contract; no end-to-end attack against a deployed
contract was run.

**Fix.** The four points are now public inputs of the decider circuit, packed into two field elements
per coordinate (`[V mod 2^253, V >> 253]`, the encoding used by `Absorbable`), and `UU.cm_*` use the
same packing. The verifier therefore folds the circuit's points with the circuit's challenge. Point
related public inputs drop from 32 to 24, and verification gas on the test circuit goes from
669,386 to 603,668. Tampering with any calldata word, the challenge, or the number of inputs is now
rejected (`test_nova_nova_decider_rejects_tampering`, `test_nova_nova_decider_evm`).

## F2. `(0,0,0)` passes the on-curve check

The on-curve constraint of `ProjectiveVar`, `Z·(Y² − b·Z²) = X·(X² + a·Z²)`, is also satisfied by
`(0,0,0)` (`test_zero_triple_passes_on_curve_check`), so a point allocated with `new_witness` can be
`(0,0,0)`. The complete addition maps any sum involving `(0,0,0)` to `(0,0,0)`, and `to_affine`
publishes it as `(0,0)`, the encoding of the identity.

In `verify_point_rlc`, a prover can therefore allocate `P₀ = (0,0,0)` whenever the genuine `P₀` is
the identity, and the circuit publishes `R = P₀ + ρ·P₁` as the identity for any `P₁` and `ρ`: it
proves `R = 0` instead of `R = ρ·P₁`. The folded primary commitments `UU.cm_e`, `UU.cm_w` are bound
only through these CycleFold public inputs, so they can be forced to the identity instead of
`U.cm + ρ·(cm_t or u.cm_w)`.

This requires a running commitment equal to the identity, which is the case for the dummy running
instance of the base case, that is, at the first step after the base case. Dropping the incoming
commitment from the fold would let the prover skip the check that the previous step's instance is
satisfiable. A complete forgery of a state transition was not constructed; the point is that the
folding relation the soundness argument relies on is not enforced.

**Fix.** A new trait `EnforceValid` rejects `y = 0 ∧ z = 0` (`Boolean::enforce_kary_nand`). It is
applied to all witness points of the CycleFold circuit and to the commitments of running and
incoming instances. For emulated affine points it is a no-op, since they have no projective
ambiguity.

## F3. Loose emulated allocation can exceed the static bounds

`LimbedVar::alloc` in `RangeCheckMode::Loose` enforces `BITS_PER_LIMB` (32) bits on every limb, while
the static `Bounds` were derived from the declared bit length. When that length is not a multiple of
32, the top limb can hold up to `2^32 − 1` although the bounds claim `2^(len mod 32)`; for example, a
variable declared with 40 bits accepted a top limb of `2^19` (`test_loose_alloc_top_limb_range`).
Loose allocation is used for the quotient in `modulo` and `enforce_congruent`, and its bounds feed
the no-overflow analysis of `mul_unaligned` and `enforce_equal_unaligned`.

A value outside the static bound could push a group sum in `enforce_equal_unaligned` out of the safe
window and make it wrap modulo the native prime, invalidating the carry argument. No concrete
exploit was found; whether it exists depends on the actual bound geometry.

**Fix.** In loose mode the length is rounded up to whole limbs, so the bounds match the constraints.
All tests still pass; the circuit shape, and therefore the keys, change slightly.

## F4. `LegoGroth16::verify` ignores mismatched input lengths

`verify` combined the public inputs with `gamma_abc_g1_pub` using `zip`, which drops the longer
side: surplus inputs were ignored and missing inputs contributed nothing. A proof for `x` was accepted
for `x ++ extra`, and a shorter `x` was checked as if the missing inputs were absent. This does not
forge a statement at a fixed interface, but `verify` should bind the whole statement. The Solidity
verifier is unaffected (fixed-size arrays).

**Fix.** `verify` rejects inputs and commitments whose lengths differ from the verification key's.

## F5. Pedersen gadgets

`PedersenGadget::msm` zipped generators with scalars and would silently drop scalars if the key were
shorter (the native `commit` returns `MessageTooLong`). This is not reachable today because
`generate_keys` checks the key length, but the circuit did not.

`PedersenCommitAndProveGadget::open` also relies on an unstated contract with `LegoGroth16`: the
committed variables must be in ascending index order across `open` calls, since the key blocks are
paired with them in that order. It holds today because the running witness allocates `e` before `w`
and opens them in that order; swapping either would silently link a commitment to the wrong
variables (see the `TODO` in `pedersen.rs`).

**Fix.** Both conditions are checked and make setup fail instead of misbehaving silently.

## F6. `enforce_equal_unaligned` carry analysis

`enforce_equal_unaligned` proves `self = other` over the integers by folding the limbs of the
difference into groups, carrying `(carry + limb) / 2^32` limb by limb and range-checking the carry
when a group is closed. The static analysis behind it had three gaps:

1. The carry bounds used a rounding (`shr_narrower`) that is only valid for integer-valued carries,
   but the carry is a field element.
2. After a group was closed, the next group started from the narrowed carry range `[lb, ub]`,
   while the range check `carry − lb < 2^bits` admits `[lb, lb + 2^bits − 1]`, up to twice as wide.
   A carry in the extra part is outside the bounds the next group's no-overflow check assumed.
3. Nothing checked that the field equation `carry · 2^(32·len) = v` implies the integer one, which
   needs `|carry · 2^(32·len) − v| < p` for every admitted `v` and carry.

If a sum wraps modulo `p`, a congruence between emulated integers can hold in the field while the
integers differ, so `modulo`, `enforce_congruent` and `evaluate_r1cs`, which all end in this
function, would accept a wrong remainder. No concrete exploit was found; whether one exists depends
on the bound geometry of a particular circuit.

**Fix.** The analysis tracks the bounds of the undivided group value, starts the next group from the
range the check actually allows, and fails synthesis unless condition 3 holds for every value in the
bounds and every admitted carry. None of the checks triggers on the circuits of the repository, so
shapes and keys are unchanged. One unit test used bounds too close to the safe window for the new
check and was narrowed.

## Observations

* The augmented circuit allocates `pp_hash` as a free witness. This is sound because the verifier
  recomputes the final hash with its own `pp_hash`; the decider uses a constant.
* `verifyProof` of the generated contract is public (inherited); only `verifyDeciderProof` carries
  the guarantees above.
* The contract's `ρ = challenge & ((1 << CHALLENGE_BITS) − 1)` matches the circuit only for the
  circuit's `CHALLENGE_BITS` (128 by default).
* Vectors are absorbed without a length prefix. Shapes are fixed by `pp_hash` and the keys, but the
  state-shape check (`same_state_shape`) is outside the circuit.
* For emulated `modulo`, the static quotient bounds and the enforced range differ. This could not be
  closed with a proof and is kept as an explicit assumption in the Lean development (`EmuArith`).
