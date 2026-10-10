import Sonobe.Circuit.Emulated.Limbs

/-!
`LimbedVar::mul_unaligned` for non-constant operands (emulated.rs:550-645), the `O(n)` product of
xJsnark: the product limbs `z_k` are hints, and the circuit enforces
`(Σ a_i c^i)(Σ b_j c^j) = Σ z_k c^k` for `c = 1, …, len` with `len = n + m − 1`.
Both sides are polynomials of degree `< len`, so they agree at `len` distinct points iff they are
equal, i.e. `z` is the convolution of `a` and `b`.
-/

namespace Sonobe
namespace Gadget

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The first `n` limbs, zero past them. -/
def tr (n : ℕ) (a : ℕ → ZMod p) : ℕ → ZMod p := fun i => if i < n then a i else 0

/-- The constraints of the polynomial identity at the points `1, …, len`. -/
def MulRel (n m : ℕ) (a b z : ℕ → ZMod p) : Prop :=
  ∀ c ∈ Finset.Icc 1 (n + m - 1),
    (∑ i ∈ range n, a i * (c : ZMod p) ^ i) * (∑ j ∈ range m, b j * (c : ZMod p) ^ j) =
      ∑ k ∈ range (n + m - 1), z k * (c : ZMod p) ^ k

noncomputable def zpoly (a : ℕ → ZMod p) (n : ℕ) : (ZMod p)[X] := ∑ i ∈ range n, C (a i) * X ^ i

theorem coeff_zpoly (a : ℕ → ZMod p) (n : ℕ) (k : ℕ) : (zpoly a n).coeff k = tr n a k := by
  simp only [zpoly, finset_sum_coeff, coeff_C_mul_X_pow, tr]
  by_cases hk : k < n
  · rw [if_pos hk, sum_eq_single k]
    · simp
    · intro j _ hjk; simp [hjk.symm]
    · intro h; exact absurd (mem_range.mpr hk) h
  · rw [if_neg hk]
    exact sum_eq_zero fun j hj => by
      have := mem_range.mp hj
      have : k ≠ j := by omega
      simp [this]

theorem natDegree_zpoly_lt (a : ℕ → ZMod p) {n : ℕ} (hn : 0 < n) : (zpoly a n).natDegree < n := by
  have : (zpoly a n).natDegree ≤ n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hi; omega)
  omega

theorem eval_zpoly (a : ℕ → ZMod p) (n : ℕ) (x : ZMod p) :
    (zpoly a n).eval x = ∑ i ∈ range n, a i * x ^ i := by
  simp [zpoly, eval_finset_sum]

/-- **The polynomial identity at `1..len` forces `z` to be the product.** -/
theorem mulRel_sound {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hlen : n + m - 1 < p) {a b z : ℕ → ZMod p}
    (h : MulRel n m a b z) : ∀ k, k < n + m - 1 → z k = conv (tr n a) (tr m b) k := by
  set Q : (ZMod p)[X] := zpoly a n * zpoly b m - zpoly z (n + m - 1) with hQ
  have hdeg : Q.natDegree < n + m - 1 := by
    have h1 := natDegree_zpoly_lt a hn
    have h2 := natDegree_zpoly_lt b hm
    have h3 : (zpoly a n * zpoly b m).natDegree ≤ (zpoly a n).natDegree + (zpoly b m).natDegree :=
      natDegree_mul_le
    have h4 : (zpoly z (n + m - 1)).natDegree ≤ n + m - 2 := by
      have : (zpoly z (n + m - 1)).natDegree ≤ n + m - 1 - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
        exact (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hi; omega)
      omega
    have h5 : Q.natDegree ≤ max (zpoly a n * zpoly b m).natDegree (zpoly z (n + m - 1)).natDegree :=
      natDegree_sub_le _ _
    omega
  have hinj : Function.Injective (fun i : Fin (n + m - 1) => ((i.val + 1 : ℕ) : ZMod p)) := by
    intro i j hij
    simp only at hij
    have := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hij
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact Fin.ext (by omega)
  have hQ0 : Q = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hinj (fun i => ?_) (by simpa using hdeg)
    have := h (i.val + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩)
    simp only [hQ, eval_sub, eval_mul, eval_zpoly]
    rw [this]; ring
  intro k hk
  have hc := congrArg (fun q => q.coeff k) hQ0
  simp only [hQ, coeff_sub, coeff_mul, coeff_zero, coeff_zpoly,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  rw [tr, if_pos hk] at hc
  have : z k = ∑ i ∈ range (k + 1), tr n a i * tr m b (k - i) := by
    have := sub_eq_zero.mp hc
    simpa [tr, if_pos hk] using this.symm
  simpa [conv] using this

end Gadget
end Sonobe
