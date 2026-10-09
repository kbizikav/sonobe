import Sonobe.Circuit.EC.Projective
import Sonobe.Circuit.Basic

/-!
`ProjectiveVar::to_affine` (short_weierstrass/mod.rs:163-197) and projective negation / selection.
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F]

/-- Constraints of `to_affine`: `inf = is_zero(z)`; witness `z_inv` with `z_inv · z = 1 - inf`;
`x' = inf ? 0 : x · z_inv`, `y' = inf ? 0 : y · z_inv`. -/
def ToAffineRel (P : PP F) (x y inf zinv inv : F) : Prop :=
  IsZeroRel P.z inf inv ∧ zinv * P.z = 1 - inf ∧
    SelectRel inf 0 (P.x * zinv) x ∧ SelectRel inf 0 (P.y * zinv) y

theorem toAffine_sound {P : PP F} {x y inf zinv inv : F} (h : ToAffineRel P x y inf zinv inv) :
    (P.z = 0 → inf = 1 ∧ x = 0 ∧ y = 0) ∧
      (P.z ≠ 0 → inf = 0 ∧ x = P.x / P.z ∧ y = P.y / P.z) := by
  obtain ⟨hz, hi, hx, hy⟩ := h
  have hinf := isZero_sound hz
  constructor
  · intro h0
    simp only [h0, if_true] at hinf
    subst hinf
    simp only [SelectRel] at hx hy
    exact ⟨rfl, by simpa using hx, by simpa using hy⟩
  · intro h0
    simp only [h0, if_false] at hinf
    subst hinf
    have hzi : zinv = 1 / P.z := by
      field_simp; linear_combination hi
    simp only [SelectRel] at hx hy
    refine ⟨rfl, ?_, ?_⟩
    · rw [hx, hzi]; simp [div_eq_mul_inv]
    · rw [hy, hzi]; simp [div_eq_mul_inv]

theorem toAffine_complete (P : PP F) :
    ∃ x y inf zinv inv, ToAffineRel P x y inf zinv inv := by
  by_cases h : P.z = 0
  · exact ⟨0, 0, 1, 0, 0, by simp [ToAffineRel, IsZeroRel, SelectRel, h]⟩
  · refine ⟨P.x / P.z, P.y / P.z, 0, 1 / P.z, 1 / P.z, ?_⟩
    simp [ToAffineRel, IsZeroRel, SelectRel, h, div_eq_mul_inv]

/-- Negation `(x, y, z) ↦ (x, -y, z)` (`ProjectiveVar::negate`). -/
def PP.neg (P : PP F) : PP F := ⟨P.x, -P.y, P.z⟩

theorem onCurve_neg {a b : F} {P : PP F} : P.neg.OnCurve a b ↔ P.OnCurve a b := by
  simp [PP.OnCurve, PP.neg]

theorem isZero_neg {P : PP F} : P.neg.IsZero ↔ P.IsZero := by
  simp [PP.IsZero, PP.neg]

variable (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

theorem pt_neg (P : PP F) : P.neg.pt W = -P.pt W := by
  by_cases hz : P.z = 0
  · rw [pt_of_z_zero W hz, pt_of_z_zero W (by simpa [PP.neg] using hz)]; simp
  · have hz' : P.neg.z ≠ 0 := hz
    by_cases h : W.toAffine.Equation (P.x / P.z) (P.y / P.z)
    · have h' : W.toAffine.Equation (P.neg.x / P.neg.z) (P.neg.y / P.neg.z) := by
        rw [equation_short] at h ⊢
        simp only [PP.neg, neg_div, neg_sq]; exact h
      rw [pt_of_equation W hz h, pt_of_equation W hz' h']
      simp [Affine.Point.mk, Affine.Point.neg_some, Affine.negY, Short.a₁ (W := W),
        Short.a₃ (W := W), PP.neg, neg_div]
    · have h' : ¬ W.toAffine.Equation (P.neg.x / P.neg.z) (P.neg.y / P.neg.z) := by
        intro h'
        apply h
        rw [equation_short] at h' ⊢
        simp only [PP.neg, neg_div, neg_sq] at h'; exact h'
      simp [PP.pt, hz, hz', h, h']

end Gadget
end Sonobe
