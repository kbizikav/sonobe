import Sonobe.Circuit.Bits

/-!
`LimbedVar::enforce_lt` against a constant (primitives/src/algebra/field/emulated.rs:386-475),
the check that makes `Tight`-allocated emulated values canonical (`value < p_target`).

Limbs are 32-bit, little endian. With `d_i = c_i - a_i`: a witness one-hot vector `b` (running sum
`r_i = Σ_{j<i} b_j`), `r_i · d_i = 0`, `Σ b = 1`, and `(Σ b_i d_i) - 1` fits in `nb` bits.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p : ℕ} [Fact p.Prime]

def LtRel (N nb : ℕ) (a : ℕ → ZMod p) (c : ℕ → ℕ) (b : ℕ → ZMod p) (pb : Fin nb → ZMod p) :
    Prop :=
  (∀ i < N, IsBool (b i)) ∧
  (∀ i < N, (∑ j ∈ range i, b j) * ((c i : ZMod p) - a i) = 0) ∧
  (∑ i ∈ range N, b i) = 1 ∧
  ToNBitsRel nb ((∑ i ∈ range N, b i * ((c i : ZMod p) - a i)) - 1) pb

/-- One-hot: boolean entries summing to one (in a field larger than `N`) have a unique `1`. -/
theorem one_hot {N : ℕ} (hN : N < p) {b : ℕ → ZMod p} (hb : ∀ i < N, IsBool (b i))
    (hs : ∑ i ∈ range N, b i = 1) :
    ∃ k < N, b k = 1 ∧ ∀ i < N, i ≠ k → b i = 0 := by
  classical
  set S := (range N).filter (fun i => b i = 1) with hS
  have hsum : ∑ i ∈ range N, b i = (S.card : ZMod p) := by
    rw [hS, Finset.card_filter, Nat.cast_sum]
    refine sum_congr rfl fun i hi => ?_
    rcases isBool_iff.mp (hb i (mem_range.mp hi)) with h | h <;> simp [h]
  have hcard : S.card = 1 := by
    have h1 : (S.card : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [← hsum, hs]; simp
    have hle : S.card ≤ N := by
      rw [hS]; exact (card_filter_le _ _).trans (by simp)
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have := (ZMod.natCast_eq_natCast_iff' S.card 1 p).mp h1
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hp1] at this
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hkS : k ∈ S := by rw [hk]; simp
  rw [hS, mem_filter, mem_range] at hkS
  refine ⟨k, hkS.1, hkS.2, fun i hi hik => ?_⟩
  rcases isBool_iff.mp (hb i hi) with h | h
  · exact h
  · exfalso
    have : i ∈ S := by rw [hS, mem_filter, mem_range]; exact ⟨hi, h⟩
    rw [hk, mem_singleton] at this
    exact hik this

/-- Partial sums of a one-hot vector. -/
theorem one_hot_prefix {N : ℕ} {b : ℕ → ZMod p} {k : ℕ} (hk : k < N) (h1 : b k = 1)
    (h0 : ∀ i < N, i ≠ k → b i = 0) {i : ℕ} (hi : i ≤ N) :
    ∑ j ∈ range i, b j = if k < i then 1 else 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih (by omega)]
    by_cases hik : i = k
    · subst hik; simp [h1]
    · rw [h0 i (by omega) hik]
      by_cases h : k < i
      · simp [h, show k < i + 1 by omega]
      · simp [h, show ¬ k < i + 1 by omega]

/-- Geometric bound used for the lexicographic argument. -/
theorem abs_sum_le (δ : ℕ → ℤ) (k : ℕ) (hδ : ∀ i < k, |δ i| ≤ 2 ^ 32 - 1) :
    |∑ i ∈ range k, δ i * 2 ^ (32 * i)| ≤ 2 ^ (32 * k) - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have ih := ih (fun i hi => hδ i (by omega))
    have h1 : |δ k * 2 ^ (32 * k)| ≤ (2 ^ 32 - 1) * 2 ^ (32 * k) := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℤ) < 2 ^ (32 * k))]
      exact mul_le_mul_of_nonneg_right (hδ k (by omega)) (by positivity)
    have : (2 : ℤ) ^ (32 * (k + 1)) = 2 ^ 32 * 2 ^ (32 * k) := by rw [mul_add, mul_one, pow_add]; ring
    calc |∑ i ∈ range k, δ i * 2 ^ (32 * i) + δ k * 2 ^ (32 * k)|
        ≤ |∑ i ∈ range k, δ i * 2 ^ (32 * i)| + |δ k * 2 ^ (32 * k)| := abs_add_le _ _
      _ ≤ (2 ^ (32 * k) - 1) + (2 ^ 32 - 1) * 2 ^ (32 * k) := add_le_add ih h1
      _ = 2 ^ (32 * (k + 1)) - 1 := by rw [this]; ring

theorem int_eq_zero_of_cast {z : ℤ} (hz : |z| < p) (h : (z : ZMod p) = 0) : z = 0 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp h
  exact Int.eq_zero_of_abs_lt_dvd this hz

/-- **`enforce_lt` is sound**: the 32-bit limbs of `a` (little endian, `N` of them) represent a
number strictly smaller than the constant `c`. -/
theorem lt_sound {N nb : ℕ} (hN : N < p) (hp : 2 ^ nb + 2 ^ 33 < p) {a : ℕ → ZMod p}
    {c : ℕ → ℕ} {b : ℕ → ZMod p} {pb : Fin nb → ZMod p}
    (ha : ∀ i < N, (a i).val < 2 ^ 32) (hc : ∀ i < N, c i < 2 ^ 32)
    (h : LtRel N nb a c b pb) :
    ∑ i ∈ range N, (a i).val * 2 ^ (32 * i) < ∑ i ∈ range N, c i * 2 ^ (32 * i) := by
  obtain ⟨hb, hr, hs, hpb⟩ := h
  obtain ⟨k, hkN, hk1, hk0⟩ := one_hot hN hb hs
  set δ : ℕ → ℤ := fun i => (c i : ℤ) - (a i).val with hδ
  have hδc : ∀ i, (((δ i : ℤ)) : ZMod p) = (c i : ZMod p) - a i := by
    intro i; simp [hδ]
  have hδb : ∀ i < N, |δ i| ≤ 2 ^ 32 - 1 := by
    intro i hi
    have h1 := ha i hi; have h2 := hc i hi
    simp only [hδ]; rw [abs_le]; constructor <;> omega
  have hpp : (2 : ℤ) ^ 32 < p := by
    have h33 : 2 ^ 33 < p := lt_of_le_of_lt (Nat.le_add_left _ _) hp
    have : (2 : ℤ) ^ 33 < p := by exact_mod_cast h33
    nlinarith
  -- digits above `k` agree
  have hup : ∀ i, k < i → i < N → δ i = 0 := by
    intro i hki hiN
    have hr' := hr i hiN
    rw [one_hot_prefix hkN hk1 hk0 hiN.le, if_pos hki, one_mul, ← hδc] at hr'
    exact int_eq_zero_of_cast (lt_of_le_of_lt (hδb i hiN) (by linarith)) hr'
  -- the digit at `k` is positive
  have hsumb : ∑ i ∈ range N, b i * ((c i : ZMod p) - a i) = ((δ k : ℤ) : ZMod p) := by
    rw [sum_eq_single k]
    · rw [hk1, one_mul, hδc]
    · intro i hi hik
      rw [hk0 i (mem_range.mp hi) hik, zero_mul]
    · intro hk; exact absurd (mem_range.mpr hkN) hk
  rw [hsumb] at hpb
  obtain ⟨hv, hlt⟩ := toNBits_sound (n := nb) (le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) hp)) hpb
  have hdk : 1 ≤ δ k := by
    set n := (((δ k : ℤ) : ZMod p) - 1).val with hn
    have hcast : (((δ k - (n + 1) : ℤ)) : ZMod p) = 0 := by
      push_cast
      have : ((n : ℕ) : ZMod p) = ((δ k : ℤ) : ZMod p) - 1 := by rw [hn]; simp
      rw [this]; ring
    have hbd : |δ k - (n + 1)| < p := by
      have h1 := hδb k hkN
      have h2 : (n : ℤ) < 2 ^ nb := by exact_mod_cast hlt
      rw [abs_lt]; rw [abs_le] at h1
      have : (2 : ℤ) ^ nb + 2 ^ 33 < p := by exact_mod_cast hp
      constructor <;> nlinarith [h1.1, h1.2]
    have := int_eq_zero_of_cast hbd hcast
    omega
  -- assemble
  have hdiff : (∑ i ∈ range N, (c i : ℤ) * 2 ^ (32 * i)) - ∑ i ∈ range N, ((a i).val : ℤ) * 2 ^ (32 * i)
      = ∑ i ∈ range N, δ i * 2 ^ (32 * i) := by
    rw [← sum_sub_distrib]; refine sum_congr rfl fun i _ => ?_; simp [hδ]; ring
  have hsplit : ∑ i ∈ range N, δ i * 2 ^ (32 * i) = ∑ i ∈ range (k + 1), δ i * 2 ^ (32 * i) := by
    rw [← sum_range_add_sum_Ico _ (show k + 1 ≤ N by omega)]
    have : ∑ i ∈ Ico (k + 1) N, δ i * 2 ^ (32 * i) = 0 := by
      refine sum_eq_zero fun i hi => ?_
      rw [hup i (by have := (mem_Ico.mp hi).1; omega) (mem_Ico.mp hi).2, zero_mul]
    rw [this, add_zero]
  have hlow := abs_sum_le δ k (fun i hi => hδb i (by omega))
  have : (0 : ℤ) < ∑ i ∈ range N, δ i * 2 ^ (32 * i) := by
    rw [hsplit, sum_range_succ]
    have hk2 : δ k * 2 ^ (32 * k) ≥ 2 ^ (32 * k) := by
      nlinarith [pow_pos (by norm_num : (0:ℤ) < 2) (32 * k)]
    have := (abs_le.mp hlow).1
    linarith
  have : ((∑ i ∈ range N, (a i).val * 2 ^ (32 * i) : ℕ) : ℤ) <
      ((∑ i ∈ range N, c i * 2 ^ (32 * i) : ℕ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast this

end Gadget
end Sonobe
