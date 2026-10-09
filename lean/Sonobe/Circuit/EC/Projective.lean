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
  if hz : P.z ≠ 0 then
    if h : W.toAffine.Equation (P.x / P.z) (P.y / P.z) then Point.mk h else 0
  else 0

theorem equation_of_onCurve {P : PP F} (hz : P.z ≠ 0) (h : P.OnCurve W.a₄ W.a₆) :
    W.toAffine.Equation (P.x / P.z) (P.y / P.z) := by
  rw [equation_short]
  unfold PP.OnCurve at h
  field_simp
  linear_combination h

theorem pt_of_equation {P : PP F} (hz : P.z ≠ 0) (h : W.toAffine.Equation (P.x / P.z) (P.y / P.z)) :
    P.pt W = Point.mk h := by
  simp [PP.pt, hz, h]

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

theorem onCurve_of_ratio {R : PP F} {x₃ y₃ : F} (hx : R.x = x₃ * R.z) (hy : R.y = y₃ * R.z)
    (h : y₃ ^ 2 = x₃ ^ 3 + W.a₄ * x₃ + W.a₆) : R.OnCurve W.a₄ W.a₆ := by
  simp only [PP.OnCurve]; rw [hx, hy]; linear_combination R.z ^ 3 * h

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

end Gadget
end Sonobe
