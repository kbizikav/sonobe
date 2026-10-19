import Sonobe.Circuit.EC.Affine
import Sonobe.Circuit.EC.RCB

/-!
Projective triples as group elements, and the group-level specification of the RCB complete
addition used by ark-r1cs-std's `ProjectiveVar` (`Add`, short_weierstrass/mod.rs:608-684).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- The group element represented by a projective triple (`0` for `z = 0` and for non-curve data;
only meaningful for triples with `OnCurve ∧ ¬IsZero`). -/
noncomputable def PP.pt (P : PP F) : W.toAffine.Point :=
  if _hz : P.z ≠ 0 then
    if h : W.toAffine.Equation (P.x / P.z) (P.y / P.z) then Point.mk h else 0
  else 0

omit [W.IsElliptic] in
theorem equation_of_onCurve {P : PP F} (hz : P.z ≠ 0) (h : P.OnCurve W.a₄ W.a₆) :
    W.toAffine.Equation (P.x / P.z) (P.y / P.z) := by
  rw [equation_short]
  unfold PP.OnCurve at h
  field_simp
  linear_combination h

omit [Short W] in
theorem pt_of_equation {P : PP F} (hz : P.z ≠ 0) (h : W.toAffine.Equation (P.x / P.z) (P.y / P.z)) :
    P.pt W = Point.mk h := by
  simp [PP.pt, hz, h]

omit [Short W] in
theorem pt_of_z_zero {P : PP F} (hz : P.z = 0) : P.pt W = 0 := by simp [PP.pt, hz]

theorem onCurve_smul {a b c : F} (hc : c ≠ 0) (P : PP F) :
    (P.smul c).OnCurve a b ↔ P.OnCurve a b := by
  simp only [PP.OnCurve, PP.smul]
  constructor
  · intro h
    have : c ^ 3 * (P.z * (P.y ^ 2 - b * P.z ^ 2) - P.x * (P.x ^ 2 + a * P.z ^ 2)) = 0 := by
      linear_combination h
    have := (mul_eq_zero.mp this).resolve_left (pow_ne_zero 3 hc)
    linear_combination this
  · intro h; linear_combination c ^ 3 * h

theorem isZero_smul {c : F} (hc : c ≠ 0) (P : PP F) : (P.smul c).IsZero ↔ P.IsZero := by
  simp [PP.IsZero, PP.smul, hc]

omit [Short W] in
theorem pt_smul {c : F} (hc : c ≠ 0) (P : PP F) : (P.smul c).pt W = P.pt W := by
  by_cases hz : P.z = 0
  · rw [pt_of_z_zero W hz, pt_of_z_zero W (by simp [PP.smul, hz])]
  · have hz' : (P.smul c).z ≠ 0 := mul_ne_zero hc hz
    have e1 : (P.smul c).x / (P.smul c).z = P.x / P.z := by
      simp [PP.smul]; field_simp
    have e2 : (P.smul c).y / (P.smul c).z = P.y / P.z := by
      simp [PP.smul]; field_simp
    by_cases h : W.toAffine.Equation (P.x / P.z) (P.y / P.z)
    · rw [pt_of_equation W hz h, pt_of_equation W hz' (by rw [e1, e2]; exact h)]
      simp only [e1, e2]
    · simp [PP.pt, hz, hz', h, e1, e2]

omit [Short W] [W.IsElliptic] in
theorem onCurve_of_ratio {R : PP F} {x₃ y₃ : F} (hx : R.x = x₃ * R.z) (hy : R.y = y₃ * R.z)
    (h : y₃ ^ 2 = x₃ ^ 3 + W.a₄ * x₃ + W.a₆) : R.OnCurve W.a₄ W.a₆ := by
  simp only [PP.OnCurve]; rw [hx, hy]; linear_combination R.z ^ 3 * h

omit [Short W] in
theorem pt_of_ratio {R : PP F} {x₃ y₃ : F} (hz : R.z ≠ 0) (hx : R.x = x₃ * R.z)
    (hy : R.y = y₃ * R.z) (h₃ : W.toAffine.Equation x₃ y₃) : R.pt W = Point.mk h₃ := by
  have e1 : R.x / R.z = x₃ := by rw [hx]; field_simp
  have e2 : R.y / R.z = y₃ := by rw [hy]; field_simp
  have h' : W.toAffine.Equation (R.x / R.z) (R.y / R.z) := by rw [e1, e2]; exact h₃
  rw [pt_of_equation W hz h']
  simp only [e1, e2]

section Spec

variable [DecidableEq F] (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
include h2 hnr

/-- RCB on two normalised finite points: result is on the curve, not the zero triple, and
represents the group sum. -/
theorem nrm_spec {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) :
    (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).OnCurve W.a₄ W.a₆ ∧ ¬ (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).IsZero ∧
      (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).pt W = Point.mk h₁ + Point.mk h₂ := by
  have e₁ := (equation_short W).mp h₁
  have e₂ := (equation_short W).mp h₂
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = y₂
    · -- doubling
      subst hy
      have hy0 : y₁ ≠ 0 := by
        intro h0; apply hnr x₁; rw [h0] at e₁; linear_combination -e₁
      have hz : (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).z = 8 * y₁ ^ 3 := nrm_dbl_Z e₁
      have h8 : (8 : F) * y₁ ^ 3 ≠ 0 := by
        have : (8 : F) ≠ 0 := by
          have : (8 : F) = 2 * 2 * 2 := by norm_num
          rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
        exact mul_ne_zero this (pow_ne_zero 3 hy0)
      have hzne : (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).z ≠ 0 := by rw [hz]; exact h8
      have h2y : 2 * y₁ ≠ 0 := mul_ne_zero h2 hy0
      set l := (3 * x₁ ^ 2 + W.a₄) / (2 * y₁) with hl
      have hl' : l * (2 * y₁) = 3 * x₁ ^ 2 + W.a₄ := by rw [hl]; field_simp
      obtain ⟨h₃, hsum⟩ := double_spec W h2 h₁ hy0 hl' rfl rfl
      have hX : (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).x = (l ^ 2 - 2 * x₁) * (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).z := by
        have := nrm_dbl_X e₁
        rw [hl]; field_simp; linear_combination this
      have hY : (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).y =
          (l * (x₁ - (l ^ 2 - 2 * x₁)) - y₁) * (nrm W.a₄ W.a₆ x₁ y₁ x₁ y₁).z := by
        have := nrm_dbl_Y e₁
        rw [hl]; field_simp; linear_combination this
      have e₃ := (equation_short W).mp h₃
      refine ⟨onCurve_of_ratio W hX hY e₃, fun hz0 => hzne hz0.2.2, ?_⟩
      rw [pt_of_ratio W hzne hX hY h₃, hsum]
    · -- opposite points
      have hy' : y₂ = -y₁ := by
        have : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination e₁ - e₂
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (sub_eq_zero.mp h) hy
        · linear_combination h
      subst hy'
      have hX := nrm_neg_X e₁
      have hZ := nrm_neg_Z e₁
      have hY := nrm_neg_Y_ne h2 hnr e₁
      refine ⟨?_, fun hz0 => hY hz0.2.1, ?_⟩
      · simp only [PP.OnCurve, hX, hZ]; ring
      · rw [pt_of_z_zero W hZ]
        symm
        exact Affine.Point.add_of_Y_eq (W := W.toAffine) rfl (by
          simp [Affine.negY, Short.a₁ (W := W), Short.a₃ (W := W)])
  · -- generic addition
    have hzne := nrm_Z_ne hnr e₁ e₂ hx
    have hv : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    set l := (y₂ - y₁) / (x₂ - x₁) with hl
    have hl' : l * (x₂ - x₁) = y₂ - y₁ := by rw [hl]; field_simp
    obtain ⟨h₃, hsum⟩ := add_unchecked_spec W h₁ h₂ hx hl' rfl rfl
    have hX : (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).x = (l ^ 2 - x₁ - x₂) * (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).z := by
      have := nrm_X e₁ e₂
      rw [hl]; field_simp; linear_combination this
    have hY : (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).y =
        (l * (x₁ - (l ^ 2 - x₁ - x₂)) - y₁) * (nrm W.a₄ W.a₆ x₁ y₁ x₂ y₂).z := by
      have := nrm_Y e₁ e₂
      rw [hl]; field_simp; linear_combination this
    have e₃ := (equation_short W).mp h₃
    refine ⟨onCurve_of_ratio W hX hY e₃, fun hz0 => hzne hz0.2.2, ?_⟩
    rw [pt_of_ratio W hzne hX hY h₃, hsum]

end Spec

section Helpers

theorem PP.smul_smul (c d : F) (P : PP F) : (P.smul c).smul d = P.smul (d * c) := by
  simp only [PP.smul, PP.mk.injEq]; refine ⟨by ring, by ring, by ring⟩

theorem PP.eq_norm {P : PP F} (hz : P.z ≠ 0) : P = (PP.mk (P.x / P.z) (P.y / P.z) 1).smul P.z := by
  obtain ⟨x, y, z⟩ := P
  simp only [PP.smul, PP.mk.injEq] at *
  refine ⟨by field_simp, by field_simp, by ring⟩

omit [Short W] [W.IsElliptic] in
theorem x_zero_of_z_zero {P : PP F} (h : P.OnCurve W.a₄ W.a₆) (hz : P.z = 0) : P.x = 0 := by
  simp only [PP.OnCurve, hz] at h
  have : P.x ^ 3 = 0 := by linear_combination -h
  exact pow_eq_zero_iff (by norm_num) |>.mp this

omit [Short W] [W.IsElliptic] in
theorem y_ne_zero {P : PP F} (h : P.OnCurve W.a₄ W.a₆) (hz : P.z = 0) (hn : ¬ P.IsZero) :
    P.y ≠ 0 := by
  intro hy
  exact hn ⟨x_zero_of_z_zero W h hz, hy, hz⟩

/-- `(0 : y : 0) + (x₂ : y₂ : 1)`, identically in the ring. -/
theorem rcb_inf_left (a b y x₂ y₂ : F) :
    rcb a b ⟨0, y, 0⟩ ⟨x₂, y₂, 1⟩ = (PP.mk x₂ y₂ 1).smul (y ^ 2 * y₂) := by
  simp only [rcb, PP.smul, PP.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

end Helpers

section Spec2

variable [DecidableEq F] (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
include h2 hnr

omit h2 [Short W] in
/-- Point at infinity plus a finite point, with the finite point written as a scaled normalised
triple. -/
theorem rcb_inf_fin {y x₂ y₂ c : F} (hy : y ≠ 0) (hc : c ≠ 0)
    (hQ' : (PP.mk x₂ y₂ 1).OnCurve W.a₄ W.a₆) :
    (rcb W.a₄ W.a₆ ⟨0, y, 0⟩ ((PP.mk x₂ y₂ 1).smul c)).OnCurve W.a₄ W.a₆ ∧
      ¬ (rcb W.a₄ W.a₆ ⟨0, y, 0⟩ ((PP.mk x₂ y₂ 1).smul c)).IsZero ∧
      (rcb W.a₄ W.a₆ ⟨0, y, 0⟩ ((PP.mk x₂ y₂ 1).smul c)).pt W =
        (PP.mk 0 y 0 : PP F).pt W + ((PP.mk x₂ y₂ 1).smul c).pt W := by
  have hy2 : y₂ ≠ 0 := by
    intro h0
    apply hnr x₂
    simp only [PP.OnCurve, h0] at hQ'
    linear_combination -hQ'
  have e := rcb_smul W.a₄ W.a₆ 1 c (PP.mk 0 y 0) (PP.mk x₂ y₂ 1)
  have h1 : (PP.mk 0 y 0 : PP F).smul 1 = PP.mk 0 y 0 := by simp [PP.smul]
  rw [h1, rcb_inf_left, PP.smul_smul] at e
  rw [e]
  have hk : (1 * c) ^ 2 * (y ^ 2 * y₂) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (by simpa using hc)) (mul_ne_zero (pow_ne_zero 2 hy) hy2)
  refine ⟨(onCurve_smul hk _).mpr hQ', ?_, ?_⟩
  · intro hz; have := ((isZero_smul hk _).mp hz).2.2; simp at this
  · rw [pt_smul W hk, pt_of_z_zero W (by rfl : (PP.mk 0 y 0 : PP F).z = 0), zero_add,
      pt_smul W hc]

/-- **RCB complete addition is the group law** (on any two valid projective points): the output
is again a valid projective point and represents `P + Q`. -/
theorem rcb_spec {P Q : PP F} (hP : P.OnCurve W.a₄ W.a₆) (hQ : Q.OnCurve W.a₄ W.a₆)
    (nP : ¬ P.IsZero) (nQ : ¬ Q.IsZero) :
    (rcb W.a₄ W.a₆ P Q).OnCurve W.a₄ W.a₆ ∧ ¬ (rcb W.a₄ W.a₆ P Q).IsZero ∧
      (rcb W.a₄ W.a₆ P Q).pt W = P.pt W + Q.pt W := by
  by_cases hPz : P.z = 0 <;> by_cases hQz : Q.z = 0
  · -- both at infinity
    have hy1 := y_ne_zero W hP hPz nP
    have hy2 := y_ne_zero W hQ hQz nQ
    have hx1 := x_zero_of_z_zero W hP hPz
    have hx2 := x_zero_of_z_zero W hQ hQz
    have hR : rcb W.a₄ W.a₆ P Q = ⟨0, (P.y * Q.y) ^ 2, 0⟩ := by
      obtain ⟨x1, y1, z1⟩ := P; obtain ⟨x2, y2, z2⟩ := Q
      simp only at hx1 hx2 hPz hQz
      subst hx1 hx2 hPz hQz
      simp only [rcb, PP.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    rw [hR]
    refine ⟨by simp [PP.OnCurve], fun h => (pow_ne_zero 2 (mul_ne_zero hy1 hy2)) h.2.1, ?_⟩
    rw [pt_of_z_zero W (by rfl), pt_of_z_zero W hPz, pt_of_z_zero W hQz, add_zero]
  · -- P at infinity, Q finite
    have hy1 := y_ne_zero W hP hPz nP
    have hx1 := x_zero_of_z_zero W hP hPz
    obtain ⟨c, hcdef⟩ : ∃ c, c = Q.z := ⟨_, rfl⟩
    obtain ⟨x₂, y₂, hQe⟩ : ∃ x₂ y₂, Q = (PP.mk x₂ y₂ 1).smul c :=
      ⟨Q.x / Q.z, Q.y / Q.z, by rw [hcdef]; exact PP.eq_norm hQz⟩
    have hc : c ≠ 0 := by rw [hcdef]; exact hQz
    have hP' : P = PP.mk 0 P.y 0 := by
      obtain ⟨x, y, z⟩ := P; simp only at hx1 hPz ⊢; subst hx1 hPz; rfl
    have hQ' : (PP.mk x₂ y₂ 1).OnCurve W.a₄ W.a₆ := by
      rw [← onCurve_smul hc]; rw [← hQe]; exact hQ
    rw [hQe, hP']
    exact rcb_inf_fin W hnr hy1 hc hQ'
  · -- P finite, Q at infinity
    have hy2 := y_ne_zero W hQ hQz nQ
    have hx2 := x_zero_of_z_zero W hQ hQz
    obtain ⟨c, hcdef⟩ : ∃ c, c = P.z := ⟨_, rfl⟩
    obtain ⟨x₁, y₁, hPe⟩ : ∃ x₁ y₁, P = (PP.mk x₁ y₁ 1).smul c :=
      ⟨P.x / P.z, P.y / P.z, by rw [hcdef]; exact PP.eq_norm hPz⟩
    have hc : c ≠ 0 := by rw [hcdef]; exact hPz
    have hQ' : Q = PP.mk 0 Q.y 0 := by
      obtain ⟨x, y, z⟩ := Q; simp only at hx2 hQz ⊢; subst hx2 hQz; rfl
    have hP'' : (PP.mk x₁ y₁ 1).OnCurve W.a₄ W.a₆ := by
      rw [← onCurve_smul hc]; rw [← hPe]; exact hP
    rw [hPe, hQ', rcb_comm, add_comm]
    exact rcb_inf_fin W hnr hy2 hc hP''
  · -- both finite
    obtain ⟨c, hcdef⟩ : ∃ c, c = P.z := ⟨_, rfl⟩
    obtain ⟨d, hddef⟩ : ∃ d, d = Q.z := ⟨_, rfl⟩
    obtain ⟨x₁, y₁, hPe⟩ : ∃ x₁ y₁, P = (PP.mk x₁ y₁ 1).smul c :=
      ⟨P.x / P.z, P.y / P.z, by rw [hcdef]; exact PP.eq_norm hPz⟩
    obtain ⟨x₂, y₂, hQe⟩ : ∃ x₂ y₂, Q = (PP.mk x₂ y₂ 1).smul d :=
      ⟨Q.x / Q.z, Q.y / Q.z, by rw [hddef]; exact PP.eq_norm hQz⟩
    have hc : c ≠ 0 := by rw [hcdef]; exact hPz
    have hd : d ≠ 0 := by rw [hddef]; exact hQz
    have hP1 : (PP.mk x₁ y₁ 1).OnCurve W.a₄ W.a₆ := by
      rw [← onCurve_smul hc, ← hPe]; exact hP
    have hQ1 : (PP.mk x₂ y₂ 1).OnCurve W.a₄ W.a₆ := by
      rw [← onCurve_smul hd, ← hQe]; exact hQ
    have e₁ : W.toAffine.Equation x₁ y₁ := by
      rw [equation_short]; simp only [PP.OnCurve] at hP1; linear_combination hP1
    have e₂ : W.toAffine.Equation x₂ y₂ := by
      rw [equation_short]; simp only [PP.OnCurve] at hQ1; linear_combination hQ1
    obtain ⟨o, nz, hp⟩ := nrm_spec W h2 hnr e₁ e₂
    have hk : (c * d) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hc hd)
    rw [hPe, hQe, rcb_smul]
    refine ⟨(onCurve_smul hk _).mpr o, fun h => nz ((isZero_smul hk _).mp h), ?_⟩
    rw [pt_smul W hk, hp, pt_smul W hc, pt_smul W hd]
    have p1 : (PP.mk x₁ y₁ 1).pt W = Point.mk e₁ := by
      rw [pt_of_equation W (by simp) (by simpa using e₁)]; simp
    have p2 : (PP.mk x₂ y₂ 1).pt W = Point.mk e₂ := by
      rw [pt_of_equation W (by simp) (by simpa using e₂)]; simp
    rw [p1, p2]

end Spec2

end Gadget
end Sonobe
