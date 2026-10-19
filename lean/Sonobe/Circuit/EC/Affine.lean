import Mathlib

/-!
Affine short-Weierstrass arithmetic used by the incomplete formulas of ark-r1cs-std's
`NonZeroAffineVar::{add_unchecked, double}` (short_weierstrass/non_zero_affine.rs:46-110).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- Short Weierstrass form `y² = x³ + a x + b` (the only form sonobe uses). -/
class Short (W : WeierstrassCurve F) : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

variable (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

omit [DecidableEq F] [W.IsElliptic] in
theorem equation_short {x y : F} :
    W.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  rw [Affine.equation_iff]
  simp [Short.a₁ (W := W), Short.a₂ (W := W), Short.a₃ (W := W)]

/-- A curve whose nonzero points all have order `r > 2` has no 2-torsion: `x³ + a x + b` has no
root. -/
theorem no_two_torsion {r : ℕ} (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r)
    (hr : 2 < r) (e : F) : e ^ 3 + W.a₄ * e + W.a₆ ≠ 0 := by
  intro h
  have heq : W.toAffine.Equation e 0 := by
    rw [equation_short]; linear_combination -h
  have hns : W.toAffine.Nonsingular e 0 := equation_iff_nonsingular.mp heq
  have hneg : -(Affine.Point.some e 0 hns) = Affine.Point.some e 0 hns := by
    rw [Affine.Point.neg_some]
    congr 1
    simp [Short.a₁ (W := W), Short.a₃ (W := W)]
  have h2 : 2 • Affine.Point.some e 0 hns = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel _
  have hd := addOrderOf_dvd_of_nsmul_eq_zero h2
  rw [hord _ (Affine.Point.some_ne_zero hns)] at hd
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-- `add_unchecked` (non_zero_affine.rs:46): the constraints `λ(x₂-x₁) = y₂-y₁`,
`x₃ = λ² - x₁ - x₂`, `y₃ = λ(x₁ - x₃) - y₁` compute the group sum when `x₁ ≠ x₂`. -/
theorem add_unchecked_spec {x₁ y₁ x₂ y₂ l x₃ y₃ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hx : x₁ ≠ x₂) (hl : l * (x₂ - x₁) = y₂ - y₁)
    (hx₃ : x₃ = l ^ 2 - x₁ - x₂) (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    ∃ h₃ : W.toAffine.Equation x₃ y₃,
      Point.mk h₁ + Point.mk h₂ = Point.mk h₃ := by
  have hsl : W.toAffine.slope x₁ x₂ y₁ y₂ = l := by
    rw [slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    linear_combination hl
  have hsum := Affine.Point.add_of_X_ne (W := W.toAffine) (h₁ := (equation_iff_nonsingular.mp h₁))
    (h₂ := (equation_iff_nonsingular.mp h₂)) hx
  have ex : x₃ = W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hsl, hx₃]; simp [Affine.addX, Short.a₁ (W := W), Short.a₂ (W := W)]
  have ey : y₃ = W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) := by
    rw [hsl, hy₃, hx₃]
    simp [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, Short.a₁ (W := W), Short.a₂ (W := W), Short.a₃ (W := W)]
    ring
  subst ex ey
  exact ⟨(Affine.nonsingular_add (equation_iff_nonsingular.mp h₁) (equation_iff_nonsingular.mp h₂)
    (fun hxy => hx hxy.1)).1, hsum⟩

/-- `NonZeroAffineVar::double` (non_zero_affine.rs:72): `λ·2y₁ = 3x₁² + a`, `x₃ = λ² - 2x₁`,
`y₃ = λ(x₁ - x₃) - y₁` compute `P + P` when `y₁ ≠ 0` (no 2-torsion point). -/
theorem double_spec (h2 : (2 : F) ≠ 0) {x₁ y₁ l x₃ y₃ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (hy : y₁ ≠ 0) (hl : l * (2 * y₁) = 3 * x₁ ^ 2 + W.a₄) (hx₃ : x₃ = l ^ 2 - 2 * x₁)
    (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    ∃ h₃ : W.toAffine.Equation x₃ y₃, Point.mk h₁ + Point.mk h₁ = Point.mk h₃ := by
  have hny : y₁ ≠ W.toAffine.negY x₁ y₁ := by
    simp only [Affine.negY, Short.a₁ (W := W), Short.a₃ (W := W)]
    intro h
    apply hy
    have : (2 : F) * y₁ = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  have hsl : W.toAffine.slope x₁ x₁ y₁ y₁ = l := by
    rw [Affine.slope_of_Y_ne rfl hny]
    have hd : y₁ - W.toAffine.negY x₁ y₁ = 2 * y₁ := by
      simp only [Affine.negY, Short.a₁ (W := W), Short.a₃ (W := W)]; ring
    have : (2 : F) * y₁ ≠ 0 := mul_ne_zero h2 hy
    rw [hd]
    simp only [Short.a₁ (W := W), Short.a₂ (W := W), mul_zero, zero_mul, sub_zero, add_zero]
    field_simp
    linear_combination -hl
  have hsum := Affine.Point.add_self_of_Y_ne (W := W.toAffine)
    (h₁ := (equation_iff_nonsingular.mp h₁)) hny
  have ex : x₃ = W.toAffine.addX x₁ x₁ (W.toAffine.slope x₁ x₁ y₁ y₁) := by
    rw [hsl, hx₃]; simp [Affine.addX, Short.a₁ (W := W), Short.a₂ (W := W)]; ring
  have ey : y₃ = W.toAffine.addY x₁ x₁ y₁ (W.toAffine.slope x₁ x₁ y₁ y₁) := by
    rw [hsl, hy₃, hx₃]
    simp [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, Short.a₁ (W := W),
      Short.a₂ (W := W), Short.a₃ (W := W)]
    ring
  subst ex ey
  exact ⟨(Affine.nonsingular_add (equation_iff_nonsingular.mp h₁) (equation_iff_nonsingular.mp h₁)
    (fun hxy => hny hxy.2)).1, hsum⟩

end Gadget
end Sonobe
