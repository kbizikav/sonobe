import Sonobe.Circuit.Emulated.Bounds
import Sonobe.Circuit.Emulated.Canon

/-!
The invariant of the unaligned limbed variables of primitives/src/algebra/field/emulated.rs:
a limb vector `a : ℕ → ZMod p` is *valid* for static bounds `bs` if every limb is the image of an
integer `z i` lying in `bs i`. Limbs past the length of the variable have bounds `[0, 0]`.
`add_unaligned`, `sub_unaligned`, `mul_unaligned` preserve validity, and the integer value
`Σ z_i 2^(32 i)` is additive / multiplicative.
-/

namespace Sonobe
namespace Gadget

open Finset Polynomial

variable {p : ℕ}

/-- `a` represents the integers `z` within the bounds `bs`. -/
def Valid (bs : ℕ → Bnd) (a : ℕ → ZMod p) (z : ℕ → ℤ) : Prop :=
  ∀ i, Bnd.Mem (z i) (bs i) ∧ a i = (z i : ZMod p)

/-- Integer value of the first `N` limbs. -/
def intVal (z : ℕ → ℤ) (N : ℕ) : ℤ := ∑ i ∈ range N, z i * 2 ^ (32 * i)

/-- Limb-wise sum / difference. -/
def addB (bs cs : ℕ → Bnd) : ℕ → Bnd := fun i => (bs i).add (cs i)
def subB (bs cs : ℕ → Bnd) : ℕ → Bnd := fun i => (bs i).sub (cs i)

/-- Convolution of limb vectors (the limbs of the product). -/
def conv {α : Type*} [Semiring α] (a b : ℕ → α) : ℕ → α := fun k => ∑ i ∈ range (k + 1), a i * b (k - i)

/-- The bounds of the product, `add_many` of the corner products. -/
def mulB (bs cs : ℕ → Bnd) : ℕ → Bnd := fun k =>
  ⟨∑ i ∈ range (k + 1), ((bs i).mul (cs (k - i))).lo,
    ∑ i ∈ range (k + 1), ((bs i).mul (cs (k - i))).hi⟩

theorem valid_add {bs cs : ℕ → Bnd} {a b : ℕ → ZMod p} {z w : ℕ → ℤ} (ha : Valid bs a z) (hb : Valid cs b w) :
    Valid (addB bs cs) (fun i => a i + b i) (fun i => z i + w i) := fun i =>
  ⟨Bnd.mem_add (ha i).1 (hb i).1, by push_cast; rw [(ha i).2, (hb i).2]⟩

theorem valid_sub {bs cs : ℕ → Bnd} {a b : ℕ → ZMod p} {z w : ℕ → ℤ} (ha : Valid bs a z) (hb : Valid cs b w) :
    Valid (subB bs cs) (fun i => a i - b i) (fun i => z i - w i) := fun i =>
  ⟨Bnd.mem_sub (ha i).1 (hb i).1, by push_cast; rw [(ha i).2, (hb i).2]⟩

theorem valid_mul {bs cs : ℕ → Bnd} {a b : ℕ → ZMod p} {z w : ℕ → ℤ} (ha : Valid bs a z) (hb : Valid cs b w) :
    Valid (mulB bs cs) (conv a b) (conv z w) := fun k => by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [mulB, conv]
    exact sum_le_sum fun i _ => (Bnd.mem_mul (ha i).1 (hb (k - i)).1).1
  · simp only [mulB, conv]
    exact sum_le_sum fun i _ => (Bnd.mem_mul (ha i).1 (hb (k - i)).1).2
  · simp only [conv]
    push_cast
    exact sum_congr rfl fun i _ => by rw [(ha i).2, (hb (k - i)).2]

theorem intVal_add (z w : ℕ → ℤ) (N : ℕ) :
    intVal (fun i => z i + w i) N = intVal z N + intVal w N := by
  simp only [intVal, add_mul, sum_add_distrib]

theorem intVal_sub (z w : ℕ → ℤ) (N : ℕ) :
    intVal (fun i => z i - w i) N = intVal z N - intVal w N := by
  simp only [intVal, sub_mul, sum_sub_distrib]

/-- The polynomial `Σ_{i<n} z_i X^i`. -/
noncomputable def limbPoly (z : ℕ → ℤ) (n : ℕ) : ℤ[X] := ∑ i ∈ range n, C (z i) * X ^ i

theorem coeff_limbPoly (z : ℕ → ℤ) (n : ℕ) (hz : ∀ i, n ≤ i → z i = 0) (k : ℕ) :
    (limbPoly z n).coeff k = z k := by
  simp only [limbPoly, finset_sum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < n
  · rw [sum_eq_single k]
    · simp
    · intro j _ hjk; simp [hjk.symm]
    · intro h; exact absurd (mem_range.mpr hk) h
  · rw [hz k (not_lt.mp hk)]
    exact sum_eq_zero fun j hj => by
      have := mem_range.mp hj
      have : k ≠ j := by omega
      simp [this]

theorem eval_limbPoly (z : ℕ → ℤ) (n : ℕ) (x : ℤ) :
    (limbPoly z n).eval x = ∑ i ∈ range n, z i * x ^ i := by
  simp [limbPoly, eval_finset_sum]

theorem natDegree_limbPoly_lt (z : ℕ → ℤ) {n : ℕ} (hn : 0 < n) :
    (limbPoly z n).natDegree < n := by
  have : (limbPoly z n).natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hi; omega)
  omega

/-- The integer value of a product is the product of the integer values. -/
theorem intVal_conv {z w : ℕ → ℤ} {n m : ℕ} (hz : ∀ i, n ≤ i → z i = 0) (hw : ∀ j, m ≤ j → w j = 0)
    {N : ℕ} (hN : n + m ≤ N + 1) :
    intVal (conv z w) N = intVal z n * intVal w m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : conv z w = fun _ => 0 := by
      funext k; simp [conv, hz]
    simp [intVal, this]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : conv z w = fun _ => 0 := by
      funext k; simp [conv, hw]
    simp [intVal, this]
  set P := limbPoly z n * limbPoly w m with hP
  have hdeg : P.natDegree < N := by
    have h1 := natDegree_limbPoly_lt z hn
    have h2 := natDegree_limbPoly_lt w hm
    have h3 : P.natDegree ≤ (limbPoly z n).natDegree + (limbPoly w m).natDegree := by
      rw [hP]; exact natDegree_mul_le
    omega
  have hcoeff : ∀ k, P.coeff k = conv z w k := by
    intro k
    rw [hP, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [conv, coeff_limbPoly z n hz, coeff_limbPoly w m hw]
  have e1 := eval_eq_sum_range' hdeg ((2 : ℤ) ^ 32)
  have e2 : P.eval ((2 : ℤ) ^ 32) = intVal z n * intVal w m := by
    rw [hP, eval_mul, eval_limbPoly, eval_limbPoly]
    simp only [intVal, ← pow_mul]
  rw [← e2, e1]
  simp only [intVal, hcoeff, ← pow_mul]

end Gadget
end Sonobe
