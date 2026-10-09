import Mathlib

/-!
Renes–Costello–Batina complete projective addition (Algorithm 1), exactly as implemented by
ark-r1cs-std (short_weierstrass/mod.rs:608-684), on projective triples `(X, Y, Z)`.

Core algebra, over a field with curve `y² = x³ + a x + b` and **no root of `x³ + a x + b`**
(= no point of order 2).
-/

namespace Sonobe
namespace Gadget

variable {F : Type*} [Field F]

structure PP (F : Type*) where
  x : F
  y : F
  z : F

/-- Curve equation of `ProjectiveVar::new_variable`: `Z (Y² - b Z²) = X (X² + a Z²)`
(short_weierstrass/mod.rs:411-436). Note that `(0,0,0)` satisfies it. -/
def PP.OnCurve (a b : F) (P : PP F) : Prop :=
  P.z * (P.y ^ 2 - b * P.z ^ 2) = P.x * (P.x ^ 2 + a * P.z ^ 2)

def PP.IsZero (P : PP F) : Prop := P.x = 0 ∧ P.y = 0 ∧ P.z = 0

/-- The 15-step formula of the Rust code. -/
def rcb (a b : F) (P Q : PP F) : PP F :=
  let xx := P.x * Q.x
  let yy := P.y * Q.y
  let zz := P.z * Q.z
  let xy := (P.x + P.y) * (Q.x + Q.y) - (xx + yy)
  let xz := (P.x + P.z) * (Q.x + Q.z) - (xx + zz)
  let yz := (P.y + P.z) * (Q.y + Q.z) - (yy + zz)
  let bzz3 := a * xz + zz * (2 * b + b)
  let ymb := yy - bzz3
  let ypb := yy + bzz3
  let xx3a := 2 * xx + xx + a * zz
  let b3xz := a * (xx - a * zz) + xz * (2 * b + b)
  ⟨ymb * xy - yz * b3xz, ypb * ymb + xx3a * b3xz, ypb * yz + xy * xx3a⟩

/-- Scaling of a projective triple. -/
def PP.smul (c : F) (P : PP F) : PP F := ⟨c * P.x, c * P.y, c * P.z⟩

theorem rcb_smul (a b c d : F) (P Q : PP F) :
    rcb a b (P.smul c) (Q.smul d) = (rcb a b P Q).smul ((c * d) ^ 2) := by
  simp only [rcb, PP.smul, PP.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem rcb_comm (a b : F) (P Q : PP F) : rcb a b P Q = rcb a b Q P := by
  simp only [rcb, PP.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem rcb_zero_left (a b : F) (Q : PP F) : rcb a b ⟨0, 0, 0⟩ Q = ⟨0, 0, 0⟩ := by
  simp [rcb]

/-! ### Both points finite and normalised (`z = 1`) -/

section Normalised

variable (a b x₁ y₁ x₂ y₂ : F)

/-- `rcb` on `(x₁, y₁, 1)`, `(x₂, y₂, 1)`. -/
abbrev nrm : PP F := rcb a b ⟨x₁, y₁, 1⟩ ⟨x₂, y₂, 1⟩

variable {a b x₁ y₁ x₂ y₂}

/-- Key certificate: `Z₃ = 0` forces the root `e = ((y₁+y₂)² - (x₁+x₂)(x₂-x₁)²)/(x₂-x₁)²` of
`x³ + a x + b`, i.e. `x(Q - P)` is the abscissa of a 2-torsion point. Found by linear algebra
over `ℚ` (cofactor `D` below), checked by `grind`. -/
theorem nrm_z_cert (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b) :
    (((y₁ + y₂) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2) ^ 3
      + a * ((y₁ + y₂) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2) * (x₂ - x₁) ^ 4 + b * (x₂ - x₁) ^ 6) =
    (4 * y₂ * b + x₂ * y₂ * a + 4 * y₁ * b + 3 * y₁ * x₂ * a + y₁ * x₂ ^ 3 + 3 * x₁ * y₂ * a
      + x₁ * y₁ * a + 3 * x₁ * y₁ * x₂ ^ 2 + 3 * x₁ ^ 2 * x₂ * y₂ + x₁ ^ 3 * y₂) *
    (nrm a b x₁ y₁ x₂ y₂).z := by
  simp only [rcb]
  grind

theorem nrm_X (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b) :
    (x₂ - x₁) ^ 2 * (nrm a b x₁ y₁ x₂ y₂).x =
      ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2) * (nrm a b x₁ y₁ x₂ y₂).z := by
  simp only [rcb]; grind

theorem nrm_Y (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b) :
    (x₂ - x₁) ^ 3 * (nrm a b x₁ y₁ x₂ y₂).y =
      ((y₂ - y₁) * (x₁ * (x₂ - x₁) ^ 2 - ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2))
        - y₁ * (x₂ - x₁) ^ 3) * (nrm a b x₁ y₁ x₂ y₂).z := by
  simp only [rcb]; grind

/-- `Z₃ ≠ 0` for `x₁ ≠ x₂`, using that the cubic has no root. -/
theorem nrm_Z_ne (hnr : ∀ e : F, e ^ 3 + a * e + b ≠ 0) (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b)
    (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b) (hx : x₁ ≠ x₂) : (nrm a b x₁ y₁ x₂ y₂).z ≠ 0 := by
  intro hz
  have hv : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have := nrm_z_cert h₁ h₂
  rw [hz, mul_zero] at this
  apply hnr (((y₁ + y₂) ^ 2 - (x₁ + x₂) * (x₂ - x₁) ^ 2) / (x₂ - x₁) ^ 2)
  field_simp
  linear_combination this

/-- Doubling: `P = Q`. -/
theorem nrm_dbl_Z (h : y ^ 2 = x ^ 3 + a * x + b) : (nrm a b x y x y).z = 8 * y ^ 3 := by
  simp only [rcb]; grind

theorem nrm_dbl_X (h : y ^ 2 = x ^ 3 + a * x + b) :
    (2 * y) ^ 2 * (nrm a b x y x y).x =
      ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2) * (nrm a b x y x y).z := by
  simp only [rcb]; grind

theorem nrm_dbl_Y (h : y ^ 2 = x ^ 3 + a * x + b) :
    (2 * y) ^ 3 * (nrm a b x y x y).y =
      ((3 * x ^ 2 + a) * (x * (2 * y) ^ 2 - ((3 * x ^ 2 + a) ^ 2 - 2 * x * (2 * y) ^ 2))
        - y * (2 * y) ^ 3) * (nrm a b x y x y).z := by
  simp only [rcb]; grind

/-- Opposite points: `Q = -P`. -/
theorem nrm_neg_X (h : y ^ 2 = x ^ 3 + a * x + b) : (nrm a b x y x (-y)).x = 0 := by
  simp only [rcb]; grind

theorem nrm_neg_Z (h : y ^ 2 = x ^ 3 + a * x + b) : (nrm a b x y x (-y)).z = 0 := by
  simp only [rcb]; grind

theorem cubic_div (a b t g : F) (hg : g ≠ 0) :
    (t / g) ^ 3 + a * (t / g) + b = (t ^ 3 + a * t * g ^ 2 + b * g ^ 3) / g ^ 3 := by
  field_simp

/-- `Y₃² = f(x(2P)) (4f)³`: `Y₃ = 0` would give a root of the cubic. -/
theorem nrm_neg_Y_sq (h : y ^ 2 = x ^ 3 + a * x + b) :
    (nrm a b x y x (-y)).y ^ 2 =
      ((3 * x ^ 2 + a) ^ 2 - 8 * x * (x ^ 3 + a * x + b)) ^ 3
        + a * ((3 * x ^ 2 + a) ^ 2 - 8 * x * (x ^ 3 + a * x + b)) * (4 * (x ^ 3 + a * x + b)) ^ 2
        + b * (4 * (x ^ 3 + a * x + b)) ^ 3 := by
  simp only [rcb]; grind

theorem nrm_neg_Y_ne (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + a * e + b ≠ 0)
    (h : y ^ 2 = x ^ 3 + a * x + b) : (nrm a b x y x (-y)).y ≠ 0 := by
  intro hy
  have hf : x ^ 3 + a * x + b ≠ 0 := hnr x
  have hsq := nrm_neg_Y_sq h
  rw [hy] at hsq
  have h4 : (4 : F) * (x ^ 3 + a * x + b) ≠ 0 := by
    have : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    exact mul_ne_zero this hf
  set t := (3 * x ^ 2 + a) ^ 2 - 8 * x * (x ^ 3 + a * x + b)
  have key := cubic_div a b t (4 * (x ^ 3 + a * x + b)) h4
  apply hnr (t / (4 * (x ^ 3 + a * x + b)))
  rw [key]
  have : t ^ 3 + a * t * (4 * (x ^ 3 + a * x + b)) ^ 2 + b * (4 * (x ^ 3 + a * x + b)) ^ 3 = 0 := by
    rw [← hsq]; norm_num
  rw [this, zero_div]

end Normalised

end Gadget
end Sonobe
