import Sonobe.Circuit.Emulated.Absorb
import Sonobe.Circuit.Emulated.Canon

/-!
Completeness of the emulated-field gadgets: every canonical value has a `Tight` allocation, a
`to_bits_le` and an `absorb_into` witness.
-/

namespace Sonobe
namespace Gadget

open Finset

section Lt

variable {p : ℕ} [Fact p.Prime]

theorem sum_limbs_lt (c : ℕ → ℕ) (hc : ∀ i, c i < 2 ^ 32) :
    ∀ M, ∑ i ∈ range M, c i * 2 ^ (32 * i) < 2 ^ (32 * M)
  | 0 => by simp
  | M + 1 => by
    have := sum_limbs_lt c hc M
    have h := hc M
    rw [sum_range_succ, show 32 * (M + 1) = 32 * M + 32 by ring, pow_add]
    have : c M * 2 ^ (32 * M) + 2 ^ (32 * M) ≤ 2 ^ 32 * 2 ^ (32 * M) := by
      nlinarith [pow_pos (by norm_num : 0 < 2) (32 * M)]
    omega

/-- The highest limb where `a < c` differs. -/
theorem exists_top_diff {a c : ℕ → ℕ} (ha : ∀ i, a i < 2 ^ 32) (hc : ∀ i, c i < 2 ^ 32) :
    ∀ M, ∑ i ∈ range M, a i * 2 ^ (32 * i) < ∑ i ∈ range M, c i * 2 ^ (32 * i) →
      ∃ k < M, a k < c k ∧ ∀ i, k < i → i < M → a i = c i
  | 0, h => by simp at h
  | M + 1, h => by
    rw [sum_range_succ, sum_range_succ] at h
    have hlowc := sum_limbs_lt c hc M
    have hlowa := sum_limbs_lt a ha M
    rcases lt_trichotomy (a M) (c M) with hlt | heq | hgt
    · exact ⟨M, by omega, hlt, fun i h1 h2 => by omega⟩
    · rw [heq] at h
      have h' : ∑ i ∈ range M, a i * 2 ^ (32 * i) < ∑ i ∈ range M, c i * 2 ^ (32 * i) := by omega
      obtain ⟨k, hk, hak, hrest⟩ := exists_top_diff ha hc M h'
      refine ⟨k, by omega, hak, fun i h1 h2 => ?_⟩
      by_cases hi : i = M
      · subst hi; exact heq
      · exact hrest i h1 (by omega)
    · exfalso
      have h1 : (c M + 1) * 2 ^ (32 * M) ≤ a M * 2 ^ (32 * M) := Nat.mul_le_mul_right _ hgt
      have e : (c M + 1) * 2 ^ (32 * M) = c M * 2 ^ (32 * M) + 2 ^ (32 * M) := by ring
      have h0 := Nat.zero_le (∑ i ∈ range M, a i * 2 ^ (32 * i))
      linarith

/-- **`enforce_lt` is complete**: a value below the constant has a witness. -/
theorem lt_complete {N : ℕ} (hp : 2 ^ 32 < p) {a : ℕ → ZMod p} {c : ℕ → ℕ}
    (ha : ∀ i, (a i).val < 2 ^ 32) (hc : ∀ i, c i < 2 ^ 32)
    (hlt : ∑ i ∈ range N, (a i).val * 2 ^ (32 * i) < ∑ i ∈ range N, c i * 2 ^ (32 * i)) :
    ∃ b pb, LtRel N 32 a c b pb := by
  obtain ⟨k, hkN, hak, hrest⟩ := exists_top_diff ha hc N hlt
  set b : ℕ → ZMod p := fun i => if i = k then 1 else 0 with hb
  have hb1 : b k = 1 := by simp [hb]
  have hb0 : ∀ i < N, i ≠ k → b i = 0 := fun i _ hik => by simp [hb, hik]
  have hpre := fun i (hi : i ≤ N) => one_hot_prefix hkN hb1 hb0 hi
  have hcp : (2 : ℕ) ^ 32 < p := hp
  have hsum : ∑ i ∈ range N, b i * ((c i : ZMod p) - a i) = ((c k - (a k).val : ℕ) : ZMod p) := by
    rw [sum_eq_single k]
    · rw [hb1, one_mul, Nat.cast_sub hak.le, ZMod.natCast_zmod_val]
    · intro i hi hik; rw [hb0 i (mem_range.mp hi) hik, zero_mul]
    · intro hk; exact absurd (mem_range.mpr hkN) hk
  have hm : c k - (a k).val - 1 < 2 ^ 32 := by have := hc k; omega
  have hmp : c k - (a k).val - 1 < p := lt_trans hm hcp
  obtain ⟨pb, hpb⟩ := toNBits_complete (n := 32) (((c k - (a k).val - 1 : ℕ)) : ZMod p)
    (by rw [ZMod.val_natCast_of_lt hmp]; exact hm)
  refine ⟨b, pb, fun i _ => ?_, fun i hi => ?_, ?_, ?_⟩
  · by_cases h : i = k <;> simp [IsBool, hb, h]
  · rw [hpre i hi.le]
    by_cases hki : k < i
    · rw [if_pos hki, one_mul]
      have h := hrest i hki hi
      simp only at h
      rw [← h]; simp
    · rw [if_neg hki, zero_mul]
  · rw [hpre N le_rfl, if_pos hkN]
  · rw [hsum]
    have : ((c k - (a k).val : ℕ) : ZMod p) - 1 = ((c k - (a k).val - 1 : ℕ) : ZMod p) := by
      have : 1 ≤ c k - (a k).val := by omega
      rw [Nat.cast_sub this]; simp
    rw [this]; exact hpb

end Lt

section Canonical

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- The canonical 32-bit limbs of a value of the emulated field. -/
def limbsOf (p1 : ℕ) {p2 : ℕ} (v : ZMod p2) : ℕ → ZMod p1 := fun i => ((mlimb v.val i : ℕ) : ZMod p1)

omit [Fact (Nat.Prime p1)] [Fact (Nat.Prime p2)] in
theorem limbsOf_val (h32 : 2 ^ 32 ≤ p1) (v : ZMod p2) (i : ℕ) :
    (limbsOf p1 v i).val = mlimb v.val i :=
  ZMod.val_natCast_of_lt (lt_of_lt_of_le (mlimb_lt _ _) h32)

omit [Fact (Nat.Prime p1)] in
theorem limbsVal_limbsOf (h32 : 2 ^ 32 ≤ p1) (hp2 : p2 ≤ 2 ^ (32 * 8)) (v : ZMod p2) :
    limbsVal 8 (limbsOf p1 v) = v.val := by
  unfold limbsVal
  simp only [limbsOf_val h32]
  rw [sum_mlimb]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt v) hp2)

omit [Fact (Nat.Prime p1)] in
theorem canon_limbsOf (h32 : 2 ^ 32 ≤ p1) (hp2 : p2 ≤ 2 ^ (32 * 8)) (v : ZMod p2) :
    Canon p2 (limbsOf p1 v) :=
  ⟨fun i _ => by rw [limbsOf_val h32]; exact mlimb_lt _ _,
    by rw [limbsVal_limbsOf h32 hp2]; exact ZMod.val_lt v⟩

omit [Fact (Nat.Prime p1)] in
theorem emuV_limbsOf (h32 : 2 ^ 32 ≤ p1) (hp2 : p2 ≤ 2 ^ (32 * 8)) (v : ZMod p2) :
    emuV p2 (limbsOf p1 v) = v := by
  unfold emuV; rw [limbsVal_limbsOf h32 hp2]; exact ZMod.natCast_zmod_val v

/-- **`Tight` allocation is complete** for every value of the emulated field. -/
theorem tight_complete (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (v : ZMod p2) :
    ∃ w, TightRel 8 32 (mlimb p2) (limbsOf p1 v) w := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  have h32' : 2 ^ 32 < p1 := lt_of_lt_of_le (by omega : 2 ^ 32 < 2 ^ 32 + 2 ^ 33) hp.le
  have hlimb : ∀ i, (limbsOf p1 v i).val < 2 ^ 32 := fun i => by
    rw [limbsOf_val h32]; exact mlimb_lt _ _
  have hlt : ∑ i ∈ range 8, (limbsOf p1 v i).val * 2 ^ (32 * i) <
      ∑ i ∈ range 8, mlimb p2 i * 2 ^ (32 * i) := by
    have e1 : ∑ i ∈ range 8, (limbsOf p1 v i).val * 2 ^ (32 * i) = v.val :=
      limbsVal_limbsOf h32 hp2.le v
    have e2 := sum_mlimb p2 8
    rw [Nat.mod_eq_of_lt hp2] at e2
    rw [e1, e2]; exact ZMod.val_lt v
  obtain ⟨b, pb, hlt'⟩ := lt_complete (N := 8) h32' hlimb (fun i => mlimb_lt _ _) hlt
  have hbits : ∀ i, ∃ bb, ToNBitsRel 32 (limbsOf p1 v i) bb := fun i =>
    toNBits_complete _ (by rw [limbsOf_val h32]; exact mlimb_lt _ _)
  choose lb hlb using hbits
  exact ⟨⟨lb, b, pb⟩, fun i _ => hlb i, hlt'⟩

/-- **`absorb_into` of an emulated variable is complete**: canonical limbs with a top limb below
`2^30` have a witness whose output is the native encoding. -/
theorem emuAbs_complete (h32 : 2 ^ 32 ≤ p1) {a : ℕ → ZMod p1} (hl : ∀ i < 7, (a i).val < 2 ^ 32)
    (ht : (a 7).val < 2 ^ 30) :
    ∃ w, EmuAbsRel a w ((((limbsVal 8 a % 2 ^ 253 : ℕ)) : ZMod p1),
      (((limbsVal 8 a / 2 ^ 253 : ℕ)) : ZMod p1)) := by
  have hb : ∀ i, ∃ bb, i < 7 → ToNBitsRel 32 (a i) bb := fun i => by
    by_cases h : i < 7
    · obtain ⟨bb, hbb⟩ := toNBits_complete (n := 32) (a i) (hl i h)
      exact ⟨bb, fun _ => hbb⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose lb hlb using hb
  obtain ⟨bt, hbt⟩ := toNBits_complete (n := 30) (a 7) ht
  set w : AbsWit p1 := ⟨lb, bt⟩
  have hrel : EmuAbsRel a w
      (∑ j ∈ range 253, (if catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) j then 1 else 0) * 2 ^ j,
        if catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) 253 then 1 else 0) :=
    ⟨fun i hi => hlb i hi, hbt, rfl, rfl⟩
  obtain ⟨e1, e2⟩ := emuAbs_sound h32 hrel
  refine ⟨w, ?_⟩
  rw [← e1, ← e2]
  exact hrel

end Canonical

end Gadget
end Sonobe
