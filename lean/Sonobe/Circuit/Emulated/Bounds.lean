import Mathlib

/-!
Static bounds of limbs (`Bounds` in primitives/src/algebra/field/emulated.rs:57-145), as pure
functions on integer intervals, with the soundness of the interval arithmetic.
-/

namespace Sonobe
namespace Gadget

/-- `Bounds(lb, ub)`: an integer interval. -/
structure Bnd where
  lo : ℤ
  hi : ℤ
deriving DecidableEq

namespace Bnd

/-- Membership. -/
def Mem (x : ℤ) (b : Bnd) : Prop := b.lo ≤ x ∧ x ≤ b.hi

def zero : Bnd := ⟨0, 0⟩
def add (a b : Bnd) : Bnd := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : Bnd) : Bnd := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- The product of two intervals (emulated.rs:94). -/
def mul (a b : Bnd) : Bnd :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
    max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

def shl (a : Bnd) (k : ℕ) : Bnd := ⟨a.lo * 2 ^ k, a.hi * 2 ^ k⟩

/-- Division by `2^k`, rounding the lower bound up and the upper bound down (`shr_narrower`). -/
def shrN (a : Bnd) (k : ℕ) : Bnd := ⟨-((-a.lo) / 2 ^ k), a.hi / 2 ^ k⟩

/-- The window of `filter_safe`: `[-L, L]` and width at most `L`, `L = (p - 1) / 2`. -/
def Safe (L : ℤ) (a : Bnd) : Prop := -L ≤ a.lo ∧ a.hi ≤ L ∧ a.hi - a.lo ≤ L

instance (L : ℤ) (a : Bnd) : Decidable (Safe L a) := by unfold Safe; infer_instance

/-- `filter_safe`. -/
def filterSafe (L : ℤ) (a : Bnd) : Option Bnd := if Safe L a then some a else none

theorem mem_add {x y : ℤ} {a b : Bnd} (hx : Mem x a) (hy : Mem y b) : Mem (x + y) (a.add b) :=
  ⟨by simp only [add]; linarith [hx.1, hy.1], by simp only [add]; linarith [hx.2, hy.2]⟩

theorem mem_sub {x y : ℤ} {a b : Bnd} (hx : Mem x a) (hy : Mem y b) : Mem (x - y) (a.sub b) :=
  ⟨by simp only [sub]; linarith [hx.1, hy.2], by simp only [sub]; linarith [hx.2, hy.1]⟩

theorem mem_shl {x : ℤ} {a : Bnd} (hx : Mem x a) (k : ℕ) : Mem (x * 2 ^ k) (a.shl k) := by
  have h : (0 : ℤ) < 2 ^ k := by positivity
  exact ⟨Int.mul_le_mul_of_nonneg_right hx.1 h.le, Int.mul_le_mul_of_nonneg_right hx.2 h.le⟩

theorem lin_min {l h x : ℤ} (c : ℤ) (h1 : l ≤ x) (h2 : x ≤ h) : min (l * c) (h * c) ≤ x * c := by
  rcases le_total 0 c with hc | hc
  · exact le_trans (min_le_left _ _) (Int.mul_le_mul_of_nonneg_right h1 hc)
  · exact le_trans (min_le_right _ _) (Int.mul_le_mul_of_nonpos_right h2 hc)

theorem lin_max {l h x : ℤ} (c : ℤ) (h1 : l ≤ x) (h2 : x ≤ h) : x * c ≤ max (l * c) (h * c) := by
  rcases le_total 0 c with hc | hc
  · exact le_trans (Int.mul_le_mul_of_nonneg_right h2 hc) (le_max_right _ _)
  · exact le_trans (Int.mul_le_mul_of_nonpos_right h1 hc) (le_max_left _ _)

theorem mem_mul {x y : ℤ} {a b : Bnd} (hx : Mem x a) (hy : Mem y b) : Mem (x * y) (a.mul b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Mem, mul]
  constructor
  · have e1 := lin_min y hx1 hx2
    have e2 : min (a.lo * y) (a.hi * y) ≥ min (min (a.lo * b.lo) (a.lo * b.hi))
        (min (a.hi * b.lo) (a.hi * b.hi)) := by
      have l1 := lin_min (l := b.lo) (h := b.hi) a.lo hy1 hy2
      have l2 := lin_min (l := b.lo) (h := b.hi) a.hi hy1 hy2
      -- `lin_min` is stated with the multiplier on the right; commute
      have l1' : min (a.lo * b.lo) (a.lo * b.hi) ≤ a.lo * y := by
        simpa [mul_comm] using l1
      have l2' : min (a.hi * b.lo) (a.hi * b.hi) ≤ a.hi * y := by
        simpa [mul_comm] using l2
      exact le_min (le_trans (min_le_left _ _) l1') (le_trans (min_le_right _ _) l2')
    exact le_trans e2 e1
  · have e1 := lin_max y hx1 hx2
    have e2 : max (a.lo * y) (a.hi * y) ≤ max (max (a.lo * b.lo) (a.lo * b.hi))
        (max (a.hi * b.lo) (a.hi * b.hi)) := by
      have l1 := lin_max (l := b.lo) (h := b.hi) a.lo hy1 hy2
      have l2 := lin_max (l := b.lo) (h := b.hi) a.hi hy1 hy2
      have l1' : a.lo * y ≤ max (a.lo * b.lo) (a.lo * b.hi) := by simpa [mul_comm] using l1
      have l2' : a.hi * y ≤ max (a.hi * b.lo) (a.hi * b.hi) := by simpa [mul_comm] using l2
      exact max_le (le_trans l1' (le_max_left _ _)) (le_trans l2' (le_max_right _ _))
    exact le_trans e1 e2

/-- A multiple of `2^k` inside `a` has its quotient inside `a.shrN k`. -/
theorem mem_shrN {x y : ℤ} {a : Bnd} (hx : Mem x a) (k : ℕ) (hxy : x = y * 2 ^ k) :
    Mem y (a.shrN k) := by
  have hk : (0 : ℤ) < 2 ^ k := by positivity
  subst hxy
  constructor
  · simp only [shrN]
    have : -y ≤ (-a.lo) / 2 ^ k := (Int.le_ediv_iff_mul_le hk).mpr (by nlinarith [hx.1])
    linarith
  · simp only [shrN]
    rw [Int.le_ediv_iff_mul_le hk]
    nlinarith [hx.2]

end Bnd

end Gadget
end Sonobe
