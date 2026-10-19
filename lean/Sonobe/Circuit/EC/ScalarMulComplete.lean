import Sonobe.Circuit.EC.ScalarMulSpec

/-!
Completeness of the double-and-add chain of `scalar_mul_le`: for an honest base point and boolean
bits, the incomplete affine formulas have witnesses at every step (no exceptional case).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

section Chain

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- Slope of `NonZeroAffineVar::double`. -/
noncomputable def dblL (a : F) (P : F × F) : F := (3 * P.1 ^ 2 + a) / (2 * P.2)

noncomputable def dblPt (a : F) (P : F × F) : F × F :=
  (dblL a P ^ 2 - 2 * P.1, dblL a P * (P.1 - (dblL a P ^ 2 - 2 * P.1)) - P.2)

/-- Slope of `NonZeroAffineVar::add_unchecked`. -/
noncomputable def addL (P₁ P₂ : F × F) : F := (P₂.2 - P₁.2) / (P₂.1 - P₁.1)

noncomputable def addPt (P₁ P₂ : F × F) : F × F :=
  (addL P₁ P₂ ^ 2 - P₁.1 - P₂.1, addL P₁ P₂ * (P₁.1 - (addL P₁ P₂ ^ 2 - P₁.1 - P₂.1)) - P₁.2)

/-- The multiples `m_i = 2^i Q` computed by repeated doubling. -/
noncomputable def mseq (a : F) (Q : F × F) : ℕ → F × F
  | 0 => Q
  | i + 1 => dblPt a (mseq a Q i)

/-- The accumulators. -/
noncomputable def aseq (a : F) (Q : F × F) (b : ℕ → F) : ℕ → F × F
  | 0 => Q
  | i + 1 => if b (i + 1) = 1 then addPt (aseq a Q b i) (mseq a Q (i + 1)) else aseq a Q b i

omit [Short W] [W.IsElliptic] in
theorem dbl_rel (a : F) {P : F × F} (hy : 2 * P.2 ≠ 0) :
    DblRel a P (dblPt a P) (dblL a P) := by
  refine ⟨?_, rfl, rfl⟩
  unfold dblL; exact div_mul_cancel₀ _ hy

omit [Short W] [W.IsElliptic] in
theorem add_rel {P₁ P₂ : F × F} (hx : P₁.1 ≠ P₂.1) : AddRel P₁ P₂ (addPt P₁ P₂) (addL P₁ P₂) := by
  refine ⟨?_, rfl, rfl⟩
  have : P₂.1 - P₁.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold addL; field_simp

omit [W.IsElliptic] in
theorem y_ne_zero_of_eq (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {P : F × F}
    (he : W.toAffine.Equation P.1 P.2) : 2 * P.2 ≠ 0 := by
  refine mul_ne_zero h2 fun h0 => hnr P.1 ?_
  have := (equation_short W).mp he
  rw [h0] at this; linear_combination -this

variable {q : W.toAffine.Point} {r : ℕ} (hq : addOrderOf q = r)
include hq

/-- **Invariants of the honest chain.** -/
theorem chain_inv (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {n : ℕ}
    {b : ℕ → F} {Q : F × F} (hQ : W.toAffine.Equation Q.1 Q.2) (hQq : ptOf W Q = q)
    (hn : 2 ^ n < r) :
    ∀ i, i < n →
      (W.toAffine.Equation (aseq W.a₄ Q b i).1 (aseq W.a₄ Q b i).2 ∧
        ptOf W (aseq W.a₄ Q b i) = kv (fun j => if b j = 1 then 1 else 0) i • q) ∧
      (W.toAffine.Equation (mseq W.a₄ Q i).1 (mseq W.a₄ Q i).2 ∧
        ptOf W (mseq W.a₄ Q i) = 2 ^ i • q) := by
  set bit : ℕ → ℕ := fun j => if b j = 1 then 1 else 0 with hbit
  have hbit1 : ∀ j, bit j ≤ 1 := fun j => by simp only [hbit]; split_ifs <;> omega
  have dbl : ∀ i, W.toAffine.Equation (mseq W.a₄ Q i).1 (mseq W.a₄ Q i).2 →
      ptOf W (mseq W.a₄ Q i) = 2 ^ i • q →
      W.toAffine.Equation (mseq W.a₄ Q (i + 1)).1 (mseq W.a₄ Q (i + 1)).2 ∧
        ptOf W (mseq W.a₄ Q (i + 1)) = 2 ^ (i + 1) • q := by
    intro i he hp
    exact dbl_step W q h2 hnr he hp (dbl_rel W.a₄ (y_ne_zero_of_eq W h2 hnr he))
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact hQ
    · rw [show aseq W.a₄ Q b 0 = Q from rfl, hQq]; simp [kv]
    · exact hQ
    · rw [show mseq W.a₄ Q 0 = Q from rfl, hQq]; simp
  | succ i ih =>
    intro hin
    obtain ⟨⟨hae, hap⟩, ⟨hme, hmp⟩⟩ := ih (by omega)
    obtain ⟨hm1e, hm1p⟩ := dbl i hme hmp
    have hk := kv_lt bit hbit1 i
    have hkpos := kv_pos bit i
    have hpow : 2 ^ (i + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hne : (aseq W.a₄ Q b i).1 ≠ (mseq W.a₄ Q (i + 1)).1 :=
      x_ne_of_nsmul W q hq hae hm1e hap hm1p (by omega) (by rw [pow_succ] at hpow ⊢; omega)
        (by rw [pow_succ] at hpow; omega) hkpos
    obtain ⟨hl, hx, hy⟩ := add_rel hne
    obtain ⟨h₃, hsum⟩ := add_unchecked_spec W hae hm1e hne hl hx hy
    have htp : ptOf W (addPt (aseq W.a₄ Q b i) (mseq W.a₄ Q (i + 1))) =
        (kv bit i + 2 ^ (i + 1)) • q := by
      rw [ptOf_eq W h₃, ← hsum, ← ptOf_eq W hae, ← ptOf_eq W hm1e, hap, hm1p, add_nsmul]
    by_cases hb1 : b (i + 1) = 1
    · have : aseq W.a₄ Q b (i + 1) = addPt (aseq W.a₄ Q b i) (mseq W.a₄ Q (i + 1)) := by
        simp [aseq, hb1]
      refine ⟨⟨?_, ?_⟩, hm1e, hm1p⟩
      · rw [this]; exact h₃
      · rw [this, htp]
        simp only [kv, hbit, if_pos hb1]; congr 1; ring
    · have : aseq W.a₄ Q b (i + 1) = aseq W.a₄ Q b i := by simp [aseq, hb1]
      refine ⟨⟨?_, ?_⟩, hm1e, hm1p⟩
      · rw [this]; exact hae
      · rw [this, hap]
        simp only [kv, hbit, if_neg hb1]; congr 1; ring

/-- **Completeness of the double-and-add chain**: the honest accumulators, multiples, sums and
slopes satisfy `ScalarChain`. -/
theorem chain_complete (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {n : ℕ}
    (hn1 : 1 ≤ n) {b : ℕ → F} {Q : F × F} (hQ : W.toAffine.Equation Q.1 Q.2)
    (hQq : ptOf W Q = q) (hn : 2 ^ n < r) (hb : ∀ i < n, IsBool (b i)) :
    ScalarChain W.a₄ n b Q (aseq W.a₄ Q b) (mseq W.a₄ Q)
      (fun i => addPt (aseq W.a₄ Q b (i - 1)) (mseq W.a₄ Q i))
      (fun i => addL (aseq W.a₄ Q b (i - 1)) (mseq W.a₄ Q i)) (fun i => dblL W.a₄ (mseq W.a₄ Q i)) := by
  have inv := chain_inv W hq h2 hnr (b := b) hQ hQq hn
  have hD : ∀ i, i < n → DblRel W.a₄ (mseq W.a₄ Q i) (mseq W.a₄ Q (i + 1)) (dblL W.a₄ (mseq W.a₄ Q i)) :=
    fun i hi => dbl_rel W.a₄ (y_ne_zero_of_eq W h2 hnr (inv i hi).2.1)
  refine ⟨rfl, rfl, hD 0 (by omega), ?_⟩
  intro i hi1 hin
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨⟨hae, hap⟩, ⟨hme, hmp⟩⟩ := inv j (by omega)
  obtain ⟨hm1e, hm1p⟩ := (inv (j + 1) hin).2
  set bit : ℕ → ℕ := fun j => if b j = 1 then 1 else 0 with hbit
  have hbit1 : ∀ j, bit j ≤ 1 := fun j => by simp only [hbit]; split_ifs <;> omega
  have hk := kv_lt bit hbit1 j
  have hkpos := kv_pos bit j
  have hpow : 2 ^ (j + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hme1 : W.toAffine.Equation (mseq W.a₄ Q (j + 1)).1 (mseq W.a₄ Q (j + 1)).2 := hm1e
  have hne : (aseq W.a₄ Q b j).1 ≠ (mseq W.a₄ Q (j + 1)).1 :=
    x_ne_of_nsmul W q hq hae hme1 hap hm1p (by omega) (by rw [pow_succ] at hpow ⊢; omega)
      (by rw [pow_succ] at hpow; omega) hkpos
  refine ⟨add_rel hne, ?_, hD (j + 1) hin⟩
  rcases isBool_iff.mp (hb (j + 1) hin) with h0 | h1
  · have : aseq W.a₄ Q b (j + 1) = aseq W.a₄ Q b j := by simp [aseq, h0]
    refine ⟨?_, ?_⟩ <;> simp [SelectRel, h0, this]
  · have : aseq W.a₄ Q b (j + 1) = addPt (aseq W.a₄ Q b j) (mseq W.a₄ Q (j + 1)) := by
      simp [aseq, h1]
    refine ⟨?_, ?_⟩ <;> simp [SelectRel, h1, this]

end Chain

section Honest

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- **Completeness of `scalar_mul_le`**: for a valid base point and boolean bits the gadget has a
satisfying witness, whatever the base (an infinite base is replaced by the generator). -/
theorem sm_complete (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) {n : ℕ} (hn1 : 1 ≤ n)
    (hrn : 2 ^ n < r) {G : F × F} (hG : W.toAffine.Equation G.1 G.2) {bits : ℕ → F}
    (hb : ∀ i < n, IsBool (bits i)) {P : PP F} (hP : P.OnCurve W.a₄ W.a₆) :
    ∃ w : SMWit F, SMRel W n G bits P w := by
  obtain ⟨x, y, inf, zinv, inv, hA⟩ := toAffine_complete P
  obtain ⟨hz0, hz1⟩ := toAffine_sound hA
  have hQ : W.toAffine.Equation (selF inf G.1 x) (selF inf G.2 y) := by
    by_cases hz : P.z = 0
    · obtain ⟨h1, h2', h3⟩ := hz0 hz
      simpa [selF, h1, h2', h3] using hG
    · obtain ⟨h1, h2', h3⟩ := hz1 hz
      have := equation_of_onCurve W hz hP
      simpa [selF, h1, h2', h3] using this
  set Q : F × F := (selF inf G.1 x, selF inf G.2 y) with hQdef
  have hq0 : ptOf W Q ≠ 0 := by
    rw [ptOf_eq W hQ]; exact Affine.Point.some_ne_zero _
  have hq := hord _ hq0
  refine ⟨⟨inf, zinv, inv, x, y, aseq W.a₄ Q bits, mseq W.a₄ Q,
    fun i => addPt (aseq W.a₄ Q bits (i - 1)) (mseq W.a₄ Q i),
    fun i => addL (aseq W.a₄ Q bits (i - 1)) (mseq W.a₄ Q i),
    fun i => dblL W.a₄ (mseq W.a₄ Q i)⟩, hA, ?_⟩
  exact chain_complete W hq h2 hnr hn1 hQ rfl hrn hb

end Honest

end Gadget
end Sonobe
