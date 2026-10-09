import Sonobe.Circuit.Basic
import Mathlib

/-!
Bit decomposition gadgets.

* `toNBitsLE` (sonobe `ToBitsGadgetExt::to_n_bits_le`, ops/bits.rs:53): `n` boolean witnesses with
  `Σ 2^i b_i = x`; sound without wrap-around iff `2^n ≤ p`.
* `toBitsLE` (ark `to_bits_le` = `to_non_unique_bits_le` + `enforce_in_field_le`,
  fields/fp/mod.rs:634, boolean/cmp.rs:23): additionally the lexicographic NAND chain proving
  `bits ≤ p - 1`; this makes the decomposition unique.
-/

namespace Sonobe
namespace Gadget

open Finset

/-- Value of the first `n` bits (little endian). -/
def natVal (n : ℕ) (a : ℕ → Bool) : ℕ := ∑ i ∈ range n, if a i then 2 ^ i else 0

theorem natVal_lt (n : ℕ) (a : ℕ → Bool) : natVal n a < 2 ^ n := by
  induction n with
  | zero => simp [natVal]
  | succ n ih =>
    unfold natVal at *
    rw [sum_range_succ, pow_succ]
    split_ifs <;> omega

/-- The constraint chain of `enforce_smaller_or_equal_than_le` (boolean/cmp.rs:41), read off from
its loop: at every position `i` where the constant `c` has a `0`, `kary_nand(run, a_i)` is enforced,
where `run` is the AND of the `a_j` over the more significant positions `j` with `c_j = 1`. -/
def Lex (n : ℕ) (a c : ℕ → Bool) : Prop :=
  ∀ i < n, c i = false → a i = true → ∃ j, i < j ∧ j < n ∧ c j = true ∧ a j = false

/-- The chain enforces exactly `a ≤ c` as integers. -/
theorem lex_iff_le (n : ℕ) (a c : ℕ → Bool) : Lex n a c ↔ natVal n a ≤ natVal n c := by
  induction n with
  | zero => simp [Lex, natVal]
  | succ n ih =>
    have ha := natVal_lt n a
    have hc := natVal_lt n c
    have ea : natVal (n + 1) a = natVal n a + (if a n then 2 ^ n else 0) := by
      simp [natVal, sum_range_succ]
    have ec : natVal (n + 1) c = natVal n c + (if c n then 2 ^ n else 0) := by
      simp [natVal, sum_range_succ]
    rw [ea, ec]
    cases hcn : c n <;> cases han : a n
    · -- c n = 0, a n = 0
      simp only [Bool.false_eq_true, if_false, add_zero]
      rw [← ih]
      constructor
      · intro h i hi hci hai
        obtain ⟨j, hij, hjn, hcj, haj⟩ := h i (by omega) hci hai
        refine ⟨j, hij, ?_, hcj, haj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with h | h
        · exact h
        · subst h; simp_all
      · intro h i hi hci hai
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · obtain ⟨j, hij, hjn, hcj, haj⟩ := h i hi' hci hai
          exact ⟨j, hij, by omega, hcj, haj⟩
        · subst hi'; simp_all
    · -- c n = 0, a n = 1 : a > c
      simp only [Bool.false_eq_true, if_false, if_true, add_zero]
      constructor
      · intro h
        obtain ⟨j, hij, hjn, -⟩ := h n (by omega) hcn han
        omega
      · intro h; omega
    · -- c n = 1, a n = 0 : a < c
      simp only [if_true, Bool.false_eq_true, if_false, add_zero]
      constructor
      · intro _; omega
      · intro _ i hi hci hai
        exact ⟨n, by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · subst h; simp_all, by omega, hcn, han⟩
    · -- c n = 1, a n = 1
      simp only [if_true]
      rw [show natVal n a + 2 ^ n ≤ natVal n c + 2 ^ n ↔ natVal n a ≤ natVal n c by omega, ← ih]
      constructor
      · intro h i hi hci hai
        obtain ⟨j, hij, hjn, hcj, haj⟩ := h i (by omega) hci hai
        refine ⟨j, hij, ?_, hcj, haj⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with h | h
        · exact h
        · subst h; simp_all
      · intro h i hi hci hai
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
        · obtain ⟨j, hij, hjn, hcj, haj⟩ := h i hi' hci hai
          exact ⟨j, hij, by omega, hcj, haj⟩
        · subst hi'; simp_all

/-! ### Binary representations -/

theorem natVal_exists (n m : ℕ) (hm : m < 2 ^ n) : ∃ a : ℕ → Bool, natVal n a = m := by
  induction n generalizing m with
  | zero => exact ⟨fun _ => false, by simp [natVal] at *; omega⟩
  | succ n ih =>
    by_cases h : 2 ^ n ≤ m
    · obtain ⟨a, ha⟩ := ih (m - 2 ^ n) (by rw [pow_succ] at hm; omega)
      refine ⟨fun i => if i = n then true else a i, ?_⟩
      have : natVal n (fun i => if i = n then true else a i) = natVal n a := by
        unfold natVal
        refine sum_congr rfl fun i hi => ?_
        have : i ≠ n := by have := mem_range.mp hi; omega
        simp [this]
      simp only [natVal, sum_range_succ] at *
      simp only [if_true] at *
      rw [this, ha]; omega
    · obtain ⟨a, ha⟩ := ih m (by omega)
      refine ⟨fun i => if i = n then false else a i, ?_⟩
      have : natVal n (fun i => if i = n then false else a i) = natVal n a := by
        unfold natVal
        refine sum_congr rfl fun i hi => ?_
        have : i ≠ n := by have := mem_range.mp hi; omega
        simp [this]
      simp only [natVal, sum_range_succ] at *
      simp only [if_true] at *
      rw [this, ha]; simp

theorem natVal_inj (n : ℕ) (a a' : ℕ → Bool) (h : natVal n a = natVal n a') :
    ∀ i < n, a i = a' i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have ha := natVal_lt n a
    have ha' := natVal_lt n a'
    have ea : natVal (n + 1) a = natVal n a + (if a n then 2 ^ n else 0) := by
      simp [natVal, sum_range_succ]
    have ea' : natVal (n + 1) a' = natVal n a' + (if a' n then 2 ^ n else 0) := by
      simp [natVal, sum_range_succ]
    rw [ea, ea'] at h
    have htop : a n = a' n := by
      cases h1 : a n <;> cases h2 : a' n <;> simp_all <;> omega
    have hlow : natVal n a = natVal n a' := by
      rw [htop] at h; omega
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih hlow i h
    · subst h; exact htop

/-! ### Over `ZMod p` -/

section Field

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- Bit `i` of a witness vector (`false` past the end). -/
def bitsOf (b : Fin n → ZMod p) : ℕ → Bool := fun i => if h : i < n then decide (b ⟨i, h⟩ = 1) else false

/-- `to_n_bits_le(n)`: boolean witnesses recomposing to `x` (ops/bits.rs:53-62). -/
def ToNBitsRel (n : ℕ) (x : ZMod p) (b : Fin n → ZMod p) : Prop :=
  (∀ i, IsBool (b i)) ∧ x = ∑ i, b i * 2 ^ (i : ℕ)

theorem recompose_eq (b : Fin n → ZMod p) (hb : ∀ i, IsBool (b i)) :
    ∑ i, b i * 2 ^ (i : ℕ) = ((natVal n (bitsOf b) : ℕ) : ZMod p) := by
  rw [natVal, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => (((if bitsOf b i then 2 ^ i else 0 : ℕ)) : ZMod p)) n]
  refine sum_congr rfl fun i _ => ?_
  rcases isBool_iff.mp (hb i) with h | h <;> simp [bitsOf, h]

/-- **Soundness** of `to_n_bits_le`: if `2^n ≤ p` the decomposition is the binary expansion of
`x.val`, which is `< 2^n`. -/
theorem toNBits_sound (hn : 2 ^ n ≤ p) {x : ZMod p} {b : Fin n → ZMod p}
    (h : ToNBitsRel n x b) : x.val = natVal n (bitsOf b) ∧ x.val < 2 ^ n := by
  obtain ⟨hb, hx⟩ := h
  rw [recompose_eq b hb] at hx
  have hlt : natVal n (bitsOf b) < p := lt_of_lt_of_le (natVal_lt _ _) hn
  have : x.val = natVal n (bitsOf b) := by
    rw [hx, ZMod.val_natCast_of_lt hlt]
  exact ⟨this, this ▸ natVal_lt _ _⟩

/-- **Completeness** of `to_n_bits_le`. -/
theorem toNBits_complete (x : ZMod p) (hx : x.val < 2 ^ n) : ∃ b, ToNBitsRel n x b := by
  obtain ⟨a, ha⟩ := natVal_exists n x.val hx
  refine ⟨fun i => if a i then 1 else 0, fun i => ?_, ?_⟩
  · by_cases h : a i <;> simp [IsBool, h]
  · have hb : ∀ i : Fin n, IsBool ((fun i : Fin n => if a i then (1 : ZMod p) else 0) i) := by
      intro i; by_cases h : a i <;> simp [IsBool, h]
    rw [recompose_eq _ hb]
    have : bitsOf (fun i : Fin n => if a i then (1 : ZMod p) else 0) = fun i => if i < n then a i else false := by
      funext i
      by_cases hi : i < n
      · simp only [bitsOf, hi, dif_pos]
        by_cases h : a i <;> simp [h]
      · simp [bitsOf, hi]
    rw [this]
    have h2 : natVal n (fun i => if i < n then a i else false) = natVal n a := by
      unfold natVal
      refine sum_congr rfl fun i hi => ?_
      simp [mem_range.mp hi]
    rw [h2, ha, ZMod.natCast_zmod_val]

theorem natVal_bitsOf_ofBits (a : ℕ → Bool) :
    natVal n (bitsOf (fun i : Fin n => if a i then (1 : ZMod p) else 0)) = natVal n a := by
  unfold natVal
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  by_cases h : a i <;> simp [bitsOf, hi', h]

/-- `to_bits_le` = `to_non_unique_bits_le` + `enforce_in_field_le` (fields/fp/mod.rs:634). `c` is
the bit pattern of `p - 1`. -/
def ToBitsRel (n : ℕ) (c : ℕ → Bool) (x : ZMod p) (b : Fin n → ZMod p) : Prop :=
  ToNBitsRel n x b ∧ Lex n (bitsOf b) c

/-- **Soundness** of canonical `to_bits_le`: the bits are the binary expansion of `x.val` itself
(no wrap-around), so the decomposition is canonical. -/
theorem toBits_sound {c : ℕ → Bool} (hc : natVal n c = p - 1) {x : ZMod p} {b : Fin n → ZMod p}
    (h : ToBitsRel n c x b) : x.val = natVal n (bitsOf b) := by
  obtain ⟨⟨hb, hx⟩, hl⟩ := h
  rw [recompose_eq b hb] at hx
  have hle : natVal n (bitsOf b) ≤ p - 1 := hc ▸ (lex_iff_le _ _ _).mp hl
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [hx, ZMod.val_natCast_of_lt (by omega)]

/-- Uniqueness: two canonical decompositions of the same element coincide. -/
theorem toBits_unique {c : ℕ → Bool} (hc : natVal n c = p - 1) {x : ZMod p} {b b' : Fin n → ZMod p}
    (h : ToBitsRel n c x b) (h' : ToBitsRel n c x b') : b = b' := by
  have e := (toBits_sound hc h).symm.trans (toBits_sound hc h')
  have key := natVal_inj n _ _ e
  funext i
  have := key i i.isLt
  have hb := isBool_iff.mp (h.1.1 i)
  have hb' := isBool_iff.mp (h'.1.1 i)
  simp only [bitsOf, i.isLt, dif_pos] at this
  rcases hb with e1 | e1 <;> rcases hb' with e2 | e2 <;> simp_all

/-- **Completeness** of canonical `to_bits_le` when `p ≤ 2^n`. -/
theorem toBits_complete {c : ℕ → Bool} (hc : natVal n c = p - 1) (hp : p ≤ 2 ^ n) (x : ZMod p) :
    ∃ b, ToBitsRel n c x b := by
  have hx : x.val < 2 ^ n := lt_of_lt_of_le (ZMod.val_lt x) hp
  obtain ⟨a, ha⟩ := natVal_exists n x.val hx
  obtain ⟨b, hb⟩ := toNBits_complete (n := n) x hx
  refine ⟨fun i => if a i then 1 else 0, ?_, ?_⟩
  · refine ⟨fun i => by by_cases h : a i <;> simp [IsBool, h], ?_⟩
    have hb' : ∀ i : Fin n, IsBool ((fun i : Fin n => if a i then (1 : ZMod p) else 0) i) := by
      intro i; by_cases h : a i <;> simp [IsBool, h]
    rw [recompose_eq _ hb', natVal_bitsOf_ofBits, ha, ZMod.natCast_zmod_val]
  · rw [lex_iff_le, natVal_bitsOf_ofBits, ha, hc]
    have := ZMod.val_lt x
    omega

end Field

end Gadget
end Sonobe
