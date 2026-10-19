import Sonobe.Circuit.Emulated.Shapes
import Sonobe.Circuit.Emulated.Equal
import Sonobe.Circuit.Emulated.Lt

/-!
`LimbedVar::modulo` (emulated.rs:776): reduce an unaligned limbed integer `self` modulo the
constant `m = p₂`. The quotient `q` and the remainder `r` are hints (`Loose` allocations); the
circuit enforces `q·m + r = self` over the integers (`enforce_equal_unaligned`) and `r < m`
(`enforce_lt`).

Everything static (the bounds of `q`, the number of limbs, the carry plan) is a function of the
bounds of `self`; the relation `ModRel` includes the success of the carry plan, which holds for any
circuit that could be synthesized.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- Bounds of the limbs of the constant `m` (`LimbedVar::constant`): exact. -/
def constB (m : ℕ) : ℕ → Bnd := fun i =>
  if i < 8 then ⟨(mlimb m i : ℤ), (mlimb m i : ℤ)⟩ else Bnd.zero

/-- The limbs of the constant `m` as field elements / integers. -/
def constL (p : ℕ) (m : ℕ) : ℕ → ZMod p := fun i => if i < 8 then (mlimb m i : ZMod p) else 0
def constZ (m : ℕ) : ℕ → ℤ := fun i => if i < 8 then (mlimb m i : ℤ) else 0

theorem const_valid (m : ℕ) : Valid (constB m) (constL p1 m) (constZ m) := by
  intro i
  by_cases hi : i < 8
  · simp [constB, constL, constZ, hi, Bnd.Mem]
  · simp [constB, constL, constZ, hi, Bnd.Mem, Bnd.zero]

/-- Static data of one reduction: the bounds of `self` and its number of limbs. -/
structure ModShape where
  selfB : ℕ → Bnd
  N : ℕ

namespace ModShape

variable (p2) (sh : ModShape)

/-- Bounds of the integer value of `self`. -/
def vlo : ℤ := ∑ i ∈ range sh.N, (sh.selfB i).lo * 2 ^ (32 * i)
def vhi : ℤ := ∑ i ∈ range sh.N, (sh.selfB i).hi * 2 ^ (32 * i)

/-- Bounds of the quotient: floor division by `m`. -/
def qlb : ℤ := sh.vlo / p2
def qub : ℤ := sh.vhi / p2

/-- Number of limbs of `q`: the bit length rounded up to whole limbs. -/
def nq : ℕ := (max (bitsLen (sh.qlb p2)) (bitsLen (sh.qub p2)) + 31) / 32

def qNeg : Bool := decide (sh.qlb p2 < 0)
def qPos : Bool := decide (0 < sh.qub p2)

/-- Bounds of the difference `q·m + r - self`. -/
def eB : ℕ → Bnd :=
  subB (addB (mulB (looseB (sh.qNeg p2) (sh.qPos p2) (sh.nq p2)) (constB p2)) (looseB false true 8))
    sh.selfB

/-- Number of limbs of the difference. -/
def nE : ℕ := max (max (sh.nq p2 + 7) 8) sh.N

end ModShape

/-- The constraints of `modulo`; the output is `r`. -/
def ModRel (p2 : ℕ) (sh : ModShape) (self o : ℕ → ZMod p1) : Prop :=
  ∃ (q r : ℕ → ZMod p1) (negq : ZMod p1),
    LooseRel (sh.qNeg p2) (sh.qPos p2) (sh.nq p2) q negq ∧ LooseRel false true 8 r 0 ∧
    (∃ b pb, LtRel 8 32 (tr 8 r) (mlimb p2) b pb) ∧
    (∃ vb len evs, run (((p1 : ℤ) - 1) / 2) p1 (sh.eB p2) (sh.nE p2) = some (vb, len, evs) ∧
      EqRel (fun i => conv (tr (sh.nq p2) q) (constL p1 p2) i + tr 8 r i - tr sh.N self i)
        (sh.nE p2) evs) ∧
    o = tr 8 r

theorem loose_small {ubPos : Bool} {n : ℕ} {a : ℕ → ZMod p1} {neg : ZMod p1} (hp1 : 2 ^ 32 ≤ p1)
    (h : LooseRel false ubPos n a neg) : ∀ i < n, (a i).val < 2 ^ 32 := by
  obtain ⟨ab, bits, hb, h1, h2, h3, h4⟩ := h
  intro i hi
  have hneg := h3 rfl
  rw [h4 i hi, hneg]
  simp only [mul_zero, zero_mul, sub_zero]
  exact (toNBits_sound hp1 (hb i hi)).2

theorem valid_small {n : ℕ} {a : ℕ → ZMod p1} (h : ∀ i < n, (a i).val < 2 ^ 32) :
    Valid (looseB false true n) (tr n a) (limbZ n a) := by
  intro i
  by_cases hi : i < n
  · have := h i hi
    have : ((a i).val : ℤ) < 2 ^ 32 := by exact_mod_cast this
    simp only [looseB, limbZ, tr, hi, if_true, Bnd.Mem, Bool.false_eq_true, if_false]
    refine ⟨⟨by positivity, by omega⟩, by simp⟩
  · simp [looseB, limbZ, tr, hi, Bnd.Mem, Bnd.zero]

theorem intVal_eq_of_zero (z : ℕ → ℤ) {n N : ℕ} (hnN : n ≤ N) (hz : ∀ i, n ≤ i → z i = 0) :
    intVal z N = intVal z n := by
  unfold intVal
  rw [← sum_range_add_sum_Ico _ hnN]
  have : ∑ i ∈ Ico n N, z i * 2 ^ (32 * i) = 0 :=
    sum_eq_zero fun i hi => by rw [hz i (mem_Ico.mp hi).1]; simp
  rw [this, add_zero]

omit [Fact (Nat.Prime p2)] in
theorem intVal_const (hp2 : p2 < 2 ^ (32 * 8)) : intVal (constZ p2) 8 = p2 := by
  unfold intVal constZ
  have := sum_mlimb p2 8
  rw [Nat.mod_eq_of_lt hp2] at this
  have h2 : ((∑ i ∈ range 8, mlimb p2 i * 2 ^ (32 * i) : ℕ) : ℤ) = p2 := by exact_mod_cast this
  push_cast at h2
  rw [← h2]
  refine sum_congr rfl fun i hi => ?_
  rw [if_pos (mem_range.mp hi)]

omit [Fact (Nat.Prime p1)] in
theorem valid_zero_beyond {bs : ℕ → Bnd} {a : ℕ → ZMod p1} {z : ℕ → ℤ} {n : ℕ}
    (hb : ∀ i, n ≤ i → bs i = Bnd.zero) (h : Valid bs a z) : ∀ i, n ≤ i → z i = 0 := by
  intro i hi
  have := (h i).1
  rw [hb i hi] at this
  simp only [Bnd.Mem, Bnd.zero] at this
  omega

/-- **`modulo` is sound**: the output is canonical and the input is congruent to it modulo `p₂`;
precisely `V = Q·p₂ + R` with `R` the value of the output. -/
theorem modulo_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (sh : ModShape)
    (hzb : ∀ i, sh.N ≤ i → sh.selfB i = Bnd.zero)
    {self o : ℕ → ZMod p1} {zS : ℕ → ℤ} (hS : Valid sh.selfB (tr sh.N self) zS)
    (h : ModRel p2 sh self o) :
    Canon p2 o ∧ ∃ Q : ℤ, intVal zS sh.N = Q * p2 + (limbsVal 8 o : ℤ) := by
  have hp1 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  have hp2pos : (0 : ℤ) < p2 := by exact_mod_cast (Fact.out : p2.Prime).pos
  obtain ⟨q, r, negq, hq, hr, ⟨b, pb, hlt⟩, ⟨vb, len, evs, hrun, hc⟩, rfl⟩ := h
  -- `q` has a sensible shape
  have hne : 0 < sh.nq p2 → sh.qNeg p2 = true ∨ sh.qPos p2 = true := by
    intro hn
    by_contra hcon
    push Not at hcon
    have hl : ¬ sh.qlb p2 < 0 := by
      have := hcon.1; simp [ModShape.qNeg] at this; omega
    have hu : ¬ 0 < sh.qub p2 := by
      have := hcon.2; simp [ModShape.qPos] at this; omega
    have hle : sh.vlo ≤ sh.vhi := by
      unfold ModShape.vlo ModShape.vhi
      exact sum_le_sum fun i _ => by
        have := (hS i).1
        exact Int.mul_le_mul_of_nonneg_right (by
          by_cases hi : i < sh.N
          · exact this.1.trans this.2
          · rw [hzb i (by omega)]; simp [Bnd.zero]) (by positivity)
    have hqle : sh.qlb p2 ≤ sh.qub p2 := Int.ediv_le_ediv hp2pos hle
    have h0 : sh.qlb p2 = 0 ∧ sh.qub p2 = 0 := by omega
    unfold ModShape.nq at hn
    rw [h0.1, h0.2] at hn
    simp [bitsLen] at hn
  obtain ⟨zq, hzq⟩ := loose_valid hp1 hne hq
  have hrs := loose_small hp1 hr
  have hzr := valid_small hrs
  have hm := const_valid (p1 := p1) p2
  have hd := valid_sub (valid_add (valid_mul hzq hm) hzr) hS
  have hsum := eq_unaligned_sound (p := p1) (by simpa using lt_of_lt_of_le (by norm_num) hp.le)
    (by have : ((p1 : ℤ) - 1) / 2 < p1 := by omega
        exact this) (fun i => (hd i).1) (fun i => (hd i).2) hrun hc
  -- the integer equation `Q m + R = V`
  have hnE : sh.nq p2 + 7 ≤ sh.nE p2 := by unfold ModShape.nE; omega
  have hNE : sh.N ≤ sh.nE p2 := by unfold ModShape.nE; omega
  have hn8 : 8 ≤ sh.nE p2 := by unfold ModShape.nE; omega
  have hzq0 : ∀ i, sh.nq p2 ≤ i → zq i = 0 :=
    valid_zero_beyond (fun i hi => by simp [looseB, show ¬ i < sh.nq p2 by omega]) hzq
  have hmz0 : ∀ j, 8 ≤ j → constZ p2 j = 0 := fun j hj => by simp [constZ, show ¬ j < 8 by omega]
  have hrz0 : ∀ j, 8 ≤ j → limbZ 8 r j = 0 := fun j hj => by simp [limbZ, show ¬ j < 8 by omega]
  have hSz0 : ∀ i, sh.N ≤ i → zS i = 0 := valid_zero_beyond hzb hS
  rw [intVal_sub, intVal_add, intVal_conv hzq0 hmz0 (by omega : sh.nq p2 + 8 ≤ sh.nE p2 + 1),
    intVal_const hp2, intVal_eq_of_zero _ hn8 hrz0,
    intVal_eq_of_zero _ hNE hSz0] at hsum
  -- the remainder is canonical
  have hr8 : ∀ i < 8, (tr 8 r i).val < 2 ^ 32 := fun i hi => by simpa [tr, hi] using hrs i hi
  have hlt' := lt_sound (N := 8) (nb := 32) (by omega) hp hr8 (fun i _ => mlimb_lt _ _) hlt
  have e2 := sum_mlimb p2 8
  rw [Nat.mod_eq_of_lt hp2] at e2
  have hcanon : Canon p2 (tr 8 r) := ⟨hr8, by unfold limbsVal; rw [e2] at hlt'; exact hlt'⟩
  refine ⟨hcanon, intVal zq (sh.nq p2), ?_⟩
  have hR : intVal (limbZ 8 r) 8 = (limbsVal 8 (tr 8 r) : ℤ) := by
    unfold intVal limbsVal
    push_cast
    refine sum_congr rfl fun i hi => ?_
    simp [limbZ, tr, mem_range.mp hi]
  rw [← hR]
  linarith

end Gadget
end Sonobe
