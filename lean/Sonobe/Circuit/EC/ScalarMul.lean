import Sonobe.Circuit.EC.Convert

/-!
`scalar_mul_le` (short_weierstrass/mod.rs:505, `fixed_scalar_mul_le` :287) restricted to the case
used by CycleFold: a non-zero base point and `n ≤ MODULUS_BITS - 2` boolean scalar bits, so the
projective tail is empty. The incomplete affine formulas are justified by the group order `r`.
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- Total interpretation of an affine pair. -/
noncomputable def ptOf (xy : F × F) : W.toAffine.Point :=
  if h : W.toAffine.Equation xy.1 xy.2 then Point.mk h else 0

theorem ptOf_eq {xy : F × F} (h : W.toAffine.Equation xy.1 xy.2) : ptOf W xy = Point.mk h := by
  simp [ptOf, h]

/-- Constraints of `NonZeroAffineVar::add_unchecked`. -/
def AddRel (P₁ P₂ P₃ : F × F) (l : F) : Prop :=
  l * (P₂.1 - P₁.1) = P₂.2 - P₁.2 ∧ P₃.1 = l ^ 2 - P₁.1 - P₂.1 ∧ P₃.2 = l * (P₁.1 - P₃.1) - P₁.2

/-- Constraints of `NonZeroAffineVar::double`. -/
def DblRel (a : F) (P P' : F × F) (l : F) : Prop :=
  l * (2 * P.2) = 3 * P.1 ^ 2 + a ∧ P'.1 = l ^ 2 - 2 * P.1 ∧ P'.2 = l * (P.1 - P'.1) - P.2

def SelectPair (c : F) (t f o : F × F) : Prop := SelectRel c t.1 f.1 o.1 ∧ SelectRel c t.2 f.2 o.2

/-- The double-and-add loop of `fixed_scalar_mul_le` over bits `b 0 … b (n-1)`:
`acc₀ = m₀ = Q`, `m₁ = 2 m₀`, and for `1 ≤ i < n`: `tmp = acc_{i-1} + m_i`,
`acc_i = b_i ? tmp : acc_{i-1}`, `m_{i+1} = 2 m_i`. -/
def ScalarChain (a : F) (n : ℕ) (b : ℕ → F) (Q : F × F) (acc m tmp : ℕ → F × F)
    (lamA lamD : ℕ → F) : Prop :=
  acc 0 = Q ∧ m 0 = Q ∧ DblRel a (m 0) (m 1) (lamD 0) ∧
    ∀ i, 1 ≤ i → i < n → AddRel (acc (i - 1)) (m i) (tmp i) (lamA i) ∧
      SelectPair (b i) (tmp i) (acc (i - 1)) (acc i) ∧ DblRel a (m i) (m (i + 1)) (lamD i)

/-- Integer carried by the accumulator: `1 + Σ_{1 ≤ j ≤ i} b_j 2^j`. -/
def kv (bit : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => kv bit i + bit (i + 1) * 2 ^ (i + 1)

theorem kv_lt (bit : ℕ → ℕ) (hb : ∀ i, bit i ≤ 1) : ∀ i, kv bit i < 2 ^ (i + 1)
  | 0 => by simp [kv]
  | i + 1 => by
    have := kv_lt bit hb i
    have := hb (i + 1)
    simp only [kv, pow_succ] at *
    nlinarith

theorem kv_pos (bit : ℕ → ℕ) : ∀ i, 0 < kv bit i
  | 0 => by simp [kv]
  | i + 1 => by have := kv_pos bit i; simp [kv]; omega

omit [Short W] [W.IsElliptic] in
theorem select_pair_sound {c : F} (hc : IsBool c) {t f o : F × F} (h : SelectPair c t f o) :
    o = if c = 1 then t else f := by
  obtain ⟨h1, h2⟩ := h
  have a := select_sound hc h1
  have b := select_sound hc h2
  ext <;> simp only [apply_ite Prod.fst, apply_ite Prod.snd] <;> assumption

section Chain

variable (q : W.toAffine.Point) {r : ℕ} (hq : addOrderOf q = r)
include hq

/-- The incomplete addition never meets the exceptional case: the abscissae differ. -/
theorem x_ne_of_nsmul {P₁ P₂ : F × F} (h₁ : W.toAffine.Equation P₁.1 P₁.2)
    (h₂ : W.toAffine.Equation P₂.1 P₂.2) {n₁ n₂ : ℕ} (e₁ : ptOf W P₁ = n₁ • q)
    (e₂ : ptOf W P₂ = n₂ • q) (hlt : n₁ < n₂) (hbig : n₂ < r) (hbig' : n₁ + n₂ < r)
    (hpos : 0 < n₁) : P₁.1 ≠ P₂.1 := by
  intro hx
  rw [ptOf_eq W h₁] at e₁
  rw [ptOf_eq W h₂] at e₂
  have hX := (Affine.Point.X_eq_iff (W := W.toAffine) (h₁ := (equation_iff_nonsingular.mp h₁))
    (h₂ := (equation_iff_nonsingular.mp h₂))).mp hx
  rcases hX with h | h
  · -- P₁ = P₂
    have h' : n₁ • q = n₂ • q := by
      have := Point.mk h₁ ; rw [← e₁, ← e₂]; exact h
    have : (n₂ - n₁) • q = 0 := by
      have e : n₂ • q = n₁ • q + (n₂ - n₁) • q := by
        rw [← add_nsmul]; congr 1; omega
      rw [e] at h'
      exact (add_eq_left.mp h'.symm)
    have hd := (addOrderOf_dvd_iff_nsmul_eq_zero.mpr this)
    rw [hq] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  · -- P₁ = -P₂
    have h' : n₁ • q = -(n₂ • q) := by rw [← e₁, ← e₂]; exact h
    have : (n₁ + n₂) • q = 0 := by
      rw [add_nsmul, h']; exact neg_add_cancel _
    have hd := (addOrderOf_dvd_iff_nsmul_eq_zero.mpr this)
    rw [hq] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- One doubling step `m ↦ 2 m` of the chain. -/
theorem dbl_step (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {i : ℕ}
    {m m' : F × F} {l : F} (he : W.toAffine.Equation m.1 m.2) (hp : ptOf W m = 2 ^ i • q)
    (hD : DblRel W.a₄ m m' l) :
    W.toAffine.Equation m'.1 m'.2 ∧ ptOf W m' = 2 ^ (i + 1) • q := by
  obtain ⟨hl, hx, hy⟩ := hD
  have hy0 : m.2 ≠ 0 := by
    intro h0
    apply hnr m.1
    have := (equation_short W).mp he
    rw [h0] at this; linear_combination -this
  obtain ⟨h₃, hsum⟩ := double_spec W h2 he hy0 hl hx hy
  refine ⟨h₃, ?_⟩
  rw [ptOf_eq W h₃, ← hsum, ← ptOf_eq W he, hp, ← add_nsmul, pow_succ]
  congr 1; ring

/-- **The double-and-add chain computes `kv · Q`**, with no exceptional case. -/
theorem chain_sound (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    {n : ℕ} {b : ℕ → F} {Q : F × F} {acc m tmp : ℕ → F × F} {lamA lamD : ℕ → F}
    (hQ : W.toAffine.Equation Q.1 Q.2) (hQq : ptOf W Q = q) (hn : 2 ^ n < r)
    (hb : ∀ i < n, IsBool (b i)) (hc : ScalarChain W.a₄ n b Q acc m tmp lamA lamD) :
    ∀ i, i < n →
      (W.toAffine.Equation (acc i).1 (acc i).2 ∧
        ptOf W (acc i) = kv (fun j => if b j = 1 then 1 else 0) i • q) ∧
      (W.toAffine.Equation (m i).1 (m i).2 ∧ ptOf W (m i) = 2 ^ i • q) := by
  obtain ⟨hacc0, hm0, hD0, hstep⟩ := hc
  set bit : ℕ → ℕ := fun j => if b j = 1 then 1 else 0 with hbit
  have hbit1 : ∀ j, bit j ≤ 1 := fun j => by simp only [hbit]; split_ifs <;> omega
  have hD : ∀ i < n, DblRel W.a₄ (m i) (m (i + 1)) (lamD i) := by
    intro i hi
    rcases i with _ | i
    · exact hD0
    · exact (hstep (i + 1) (by omega) hi).2.2
  have dbl : ∀ i < n, W.toAffine.Equation (m i).1 (m i).2 → ptOf W (m i) = 2 ^ i • q →
      W.toAffine.Equation (m (i + 1)).1 (m (i + 1)).2 ∧ ptOf W (m (i + 1)) = 2 ^ (i + 1) • q :=
    fun i hi he hp => dbl_step W q hq h2 hnr he hp (hD i hi)
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hacc0]; exact hQ
    · rw [hacc0, hQq]; simp [kv]
    · rw [hm0]; exact hQ
    · rw [hm0, hQq]; simp
  | succ i ih =>
    intro hin
    obtain ⟨⟨hae, hap⟩, ⟨hme, hmp⟩⟩ := ih (by omega)
    obtain ⟨hm1e, hm1p⟩ := dbl i (by omega) hme hmp
    obtain ⟨hadd, hsel, -⟩ := hstep (i + 1) (by omega) hin
    simp only [Nat.add_sub_cancel] at hadd hsel
    -- bounds for the exceptional-case argument
    have hk := kv_lt bit hbit1 i
    have hkpos := kv_pos bit i
    have hpow : 2 ^ (i + 2) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hne : (acc i).1 ≠ (m (i + 1)).1 :=
      x_ne_of_nsmul W q hq hae hm1e hap hm1p (by omega) (by rw [pow_succ] at hpow ⊢; omega)
        (by rw [pow_succ] at hpow; omega) hkpos
    obtain ⟨hl, hx, hy⟩ := hadd
    obtain ⟨h₃, hsum⟩ := add_unchecked_spec W hae hm1e hne hl hx hy
    have htp : ptOf W (tmp (i + 1)) = (kv bit i + 2 ^ (i + 1)) • q := by
      rw [ptOf_eq W h₃, ← hsum, ← ptOf_eq W hae, ← ptOf_eq W hm1e, hap, hm1p, add_nsmul]
    have hsel' := select_pair_sound (hb (i + 1) hin) hsel
    by_cases hb1 : b (i + 1) = 1
    · rw [if_pos hb1] at hsel'
      refine ⟨⟨?_, ?_⟩, hm1e, hm1p⟩
      · rw [hsel']; exact h₃
      · rw [hsel', htp]
        simp only [kv, hbit, if_pos hb1]; congr 1; ring
    · rw [if_neg hb1] at hsel'
      refine ⟨⟨?_, ?_⟩, hm1e, hm1p⟩
      · rw [hsel']; exact hae
      · rw [hsel', hap]
        simp only [kv, hbit, if_neg hb1]; congr 1; ring

end Chain

end Gadget
end Sonobe

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- The constant `zero` point of `ProjectiveVar`: `(0, 1, 0)`. -/
def zeroPP : PP F := ⟨0, 1, 0⟩

/-- `CondSelectGadget` on projective variables: `c ? t : f`, componentwise. -/
def selPP (c : F) (t f : PP F) : PP F :=
  ⟨c * (t.x - f.x) + f.x, c * (t.y - f.y) + f.y, c * (t.z - f.z) + f.z⟩

theorem selPP_one (t f : PP F) : selPP 1 t f = t := by simp [selPP]
theorem selPP_zero (t f : PP F) : selPP 0 t f = f := by simp [selPP]

theorem zeroPP_onCurve (a b : F) : (zeroPP : PP F).OnCurve a b := by simp [zeroPP, PP.OnCurve]
theorem zeroPP_not_isZero : ¬ (zeroPP : PP F).IsZero := by simp [zeroPP, PP.IsZero]
theorem zeroPP_pt : (zeroPP : PP F).pt W = 0 := pt_of_z_zero W rfl

/-- A normalised finite point `(x, y, 1)`. -/
def finPP (xy : F × F) : PP F := ⟨xy.1, xy.2, 1⟩

theorem finPP_onCurve (hE : W.toAffine.Equation xy.1 xy.2) : (finPP xy).OnCurve W.a₄ W.a₆ := by
  have := (equation_short W).mp hE
  simp only [finPP, PP.OnCurve]; linear_combination this

theorem finPP_not_isZero (xy : F × F) : ¬ (finPP xy).IsZero := by simp [finPP, PP.IsZero]

theorem finPP_pt (hE : W.toAffine.Equation xy.1 xy.2) : (finPP xy).pt W = ptOf W xy := by
  rw [pt_of_equation W (by simp [finPP]) (by simpa [finPP] using hE), ptOf_eq W hE]
  simp [finPP]

end Gadget
end Sonobe
