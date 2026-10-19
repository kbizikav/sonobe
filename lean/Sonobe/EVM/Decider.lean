import Sonobe.Snark.CPSound
import Sonobe.Circuit.Coords

/-!
The generated EVM verifier (`cyclefold_based_ivc_decider.sol.askama` + `legogroth16.sol.askama`)
at the level of 256-bit words.

Words are natural numbers. The BN254 precompiles are modelled as partial functions: `ecAdd`/`ecMul`
(0x06/0x07) revert on coordinates `≥ q` and on points off the curve, `(0, 0)` is the identity, and
the result is the canonical encoding of the group operation. The pairing precompile (0x08) is
abstracted by the pairing equations of `LegoGroth16.Accepts` (the contract's `e(·) = 1` product is
that equation in additive notation), after decoding the proof words.
-/

namespace Sonobe
namespace EVM

open WeierstrassCurve WeierstrassCurve.Affine Sonobe.Gadget
open scoped Classical

noncomputable local instance decEqZModEvm {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

section Precompiles

variable {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve (ZMod q)) [Short W] [W.IsElliptic]

/-- A pair of words as an affine point; `(0, 0)` is the identity; invalid input is `none`. -/
noncomputable def decodeG1 (a : ℕ × ℕ) : Option W.toAffine.Point :=
  if a.1 < q ∧ a.2 < q then
    if a = (0, 0) then some 0
    else if hE : W.toAffine.Equation (a.1 : ZMod q) (a.2 : ZMod q) then
      some (Point.some (a.1 : ZMod q) (a.2 : ZMod q) ((equation_iff_nonsingular).mp hE))
    else none
  else none

/-- Canonical words of a point. -/
noncomputable def encodeG1 (P : W.toAffine.Point) : ℕ × ℕ :=
  ((coordsOf W P).1.val, (coordsOf W P).2.val)

theorem decode_encode (hb : W.a₆ ≠ 0) (P : W.toAffine.Point) :
    decodeG1 W (encodeG1 W P) = some P := by
  cases P with
  | zero =>
    have hq : 0 < q := (Fact.out : q.Prime).pos
    simp [decodeG1, encodeG1, coordsOf, hq]
    rfl
  | some x y h =>
    have hq : 0 < q := (Fact.out : q.Prime).pos
    have hE : W.toAffine.Equation x y := (equation_iff_nonsingular).mpr h
    have hne : (x, y) ≠ (0, 0) := by
      intro h0
      simp only [Prod.mk.injEq] at h0
      have := (equation_short W).mp hE
      rw [h0.1, h0.2] at this
      apply hb; simpa using this.symm
    have h1 : (x.val : ZMod q) = x := ZMod.natCast_zmod_val x
    have h2 : (y.val : ZMod q) = y := ZMod.natCast_zmod_val y
    have hne' : ¬ (x.val = 0 ∧ y.val = 0) := by
      rintro ⟨a, b⟩
      apply hne
      rw [ZMod.val_eq_zero] at a b
      simp [a, b]
    simp only [decodeG1, encodeG1, coordsOf]
    rw [if_pos ⟨ZMod.val_lt x, ZMod.val_lt y⟩, if_neg (by simpa [Prod.ext_iff] using hne')]
    have hE' : W.toAffine.Equation (x.val : ZMod q) (y.val : ZMod q) := by rw [h1, h2]; exact hE
    rw [dif_pos hE']
    simp only [h1, h2]

/-- `ecAdd` (0x06). -/
noncomputable def ecAdd (a b : ℕ × ℕ) : Option (ℕ × ℕ) :=
  (decodeG1 W a).bind fun P => (decodeG1 W b).map fun Q => encodeG1 W (P + Q)

/-- `ecMul` (0x07): the scalar is any word. -/
noncomputable def ecMul (a : ℕ × ℕ) (s : ℕ) : Option (ℕ × ℕ) :=
  (decodeG1 W a).map fun P => encodeG1 W (s • P)

omit [Short W] in
theorem decode_some {a : ℕ × ℕ} {P : W.toAffine.Point} (h : decodeG1 W a = some P) :
    a.1 < q ∧ a.2 < q ∧ encodeG1 W P = a := by
  unfold decodeG1 at h
  by_cases hlt : a.1 < q ∧ a.2 < q
  · rw [if_pos hlt] at h
    refine ⟨hlt.1, hlt.2, ?_⟩
    by_cases h0 : a = (0, 0)
    · rw [if_pos h0] at h
      obtain rfl := Option.some.inj h
      subst h0
      simp [encodeG1, coordsOf]
    · rw [if_neg h0] at h
      by_cases hE : W.toAffine.Equation (a.1 : ZMod q) (a.2 : ZMod q)
      · rw [dif_pos hE] at h
        obtain rfl := Option.some.inj h
        simp [encodeG1, coordsOf, ZMod.val_natCast_of_lt hlt.1, ZMod.val_natCast_of_lt hlt.2]
      · rw [dif_neg hE] at h; exact absurd h (by simp)
  · rw [if_neg hlt] at h; exact absurd h (by simp)

/-- `_ecAdd(a, _ecMul(b, ρ))` (the fold fragment of the Nova adapter). -/
noncomputable def foldC (a b : ℕ × ℕ) (ρ : ℕ) : Option (ℕ × ℕ) := (ecMul W b ρ).bind (ecAdd W a)

theorem foldC_spec (hb : W.a₆ ≠ 0) {a b : ℕ × ℕ} {ρ : ℕ} {c : ℕ × ℕ}
    (h : foldC W a b ρ = some c) :
    ∃ PA PB, decodeG1 W a = some PA ∧ decodeG1 W b = some PB ∧ c = encodeG1 W (PA + ρ • PB) := by
  unfold foldC ecMul ecAdd at h
  cases hB : decodeG1 W b with
  | none => simp [hB] at h
  | some PB =>
    simp only [hB, Option.map_some, Option.bind_some] at h
    cases hA : decodeG1 W a with
    | none => simp [hA] at h
    | some PA =>
      simp only [hA, decode_encode W hb, Option.map_some, Option.bind_some] at h
      exact ⟨PA, PB, rfl, rfl, (Option.some.inj h).symm⟩

end Precompiles

section Contract

variable {p1 q sN : ℕ} [Fact p1.Prime] [Fact q.Prime] (W1 : WeierstrassCurve (ZMod q)) [Short W1]
  [W1.IsElliptic] {PW : Type*}

/-- Calldata of `verifyDeciderProof` (`PW`: the 12 proof words). The state is flattened. -/
structure Calldata (sN : ℕ) (PW : Type*) where
  i : ℕ
  z0 : Fin sN → ℕ
  zi : Fin sN → ℕ
  challenge : ℕ
  uCmE : ℕ × ℕ
  uCmW : ℕ × ℕ
  ucmW : ℕ × ℕ
  cmT : ℕ × ℕ
  proof : PW

/-- `_pack`: low 253 bits and the remaining bit. -/
def packLo (v : ℕ) : ℕ := v % 2 ^ 253
def packHi (v : ℕ) : ℕ := v / 2 ^ 253

/-- Coordinates of the six points `U.cm_e, U.cm_w, u.cm_w, cm_t, cm_e, cm_w`, in the order
`x₀, y₀, x₁, y₁, …`. -/
def coordW (pts : Fin 6 → ℕ × ℕ) (k : Fin 12) : ℕ :=
  if k.val % 2 = 0 then (pts ⟨k.val / 2, by omega⟩).1 else (pts ⟨k.val / 2, by omega⟩).2

/-- The array `x` of public inputs the contract builds (after the range checks):
`[i, z₀.., zᵢ.., challenge, pack(coords)..]`. -/
def xList (cd : Calldata sN PW) (pts : Fin 6 → ℕ × ℕ) : List ℕ :=
  [cd.i] ++ List.ofFn cd.z0 ++ List.ofFn cd.zi ++ [cd.challenge] ++
    (List.ofFn fun k : Fin 12 => [packLo (coordW pts k), packHi (coordW pts k)]).flatten

/-- The six points: the four calldata points and the two folded commitments. -/
def ptsOf (cd : Calldata sN PW) (ce cw : ℕ × ℕ) : Fin 6 → ℕ × ℕ :=
  ![cd.uCmE, cd.uCmW, cd.ucmW, cd.cmT, ce, cw]

/-- Interpret a list as a vector (`0` past the end). -/
def vecOfList {F : Type*} [Zero F] (L : List F) (n : ℕ) : Fin n → F := fun k => L.getD k 0

variable {G₂ G_T : Type*} [AddCommGroup G₂] [Module (ZMod p1) G₂] [AddCommGroup G_T]
  [Module (ZMod p1) G_T] [Module (ZMod p1) W1.toAffine.Point]

/-- `LegoGroth16Verifier.verifyProof(x, c, proof)`: every input word is `< R` (the scalar field
order `p1`), the commitments and proof words are valid points (checked by the pairing
precompile), and the pairing equations hold. -/
def VerifyProof (e : W1.toAffine.Point →ₗ[ZMod p1] G₂ →ₗ[ZMod p1] G_T) {ld : ℕ}
    (vk : LegoGroth16.VK W1.toAffine.Point G₂ ld 2)
    (decodeProof : PW → Option (LegoGroth16.Proof W1.toAffine.Point G₂))
    (xs : List ℕ) (c : Fin 2 → ℕ × ℕ) (pw : PW) : Prop :=
  xs.length = ld ∧ (∀ w ∈ xs, w < p1) ∧
    ∃ (cG : Fin 2 → W1.toAffine.Point) (π : LegoGroth16.Proof W1.toAffine.Point G₂),
      (∀ j, decodeG1 W1 (c j) = some (cG j)) ∧ decodeProof pw = some π ∧
      LegoGroth16.Accepts e vk (vecOfList (xs.map (fun w => (w : ZMod p1))) ld) cG π

/-- `DeciderVerifier.verifyDeciderProof` accepts. -/
def DeciderAccepts (e : W1.toAffine.Point →ₗ[ZMod p1] G₂ →ₗ[ZMod p1] G_T) {ld : ℕ}
    (vk : LegoGroth16.VK W1.toAffine.Point G₂ ld 2)
    (decodeProof : PW → Option (LegoGroth16.Proof W1.toAffine.Point G₂))
    (cd : Calldata sN PW) : Prop :=
  (cd.i = 0 ∧ cd.z0 = cd.zi) ∨
    (cd.i ≠ 0 ∧ ∃ ce cw, foldC W1 cd.uCmE cd.cmT (cd.challenge % 2 ^ 128) = some ce ∧
      foldC W1 cd.uCmW cd.ucmW (cd.challenge % 2 ^ 128) = some cw ∧
      VerifyProof W1 e vk decodeProof (xList cd (ptsOf cd ce cw)) ![ce, cw] cd.proof)

end Contract

end EVM
end Sonobe
