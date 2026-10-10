import Sonobe.Circuit.Emulated.Mul

/-!
The static bounds of the limbed variables that the arithmetic gadgets start from
(`compute_bounds` and the allocations of emulated.rs): `Tight` values of the emulated field,
variables built from bits (`from_bits_le`), and constants. Each comes with its link to `Valid`.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- Bit length of the magnitude of an integer (`BigInt::bits`). -/
def bitsLen (x : ℤ) : ℕ := x.natAbs.size

/-- `compute_bounds` for 32-bit limbs (emulated.rs:1102). -/
def computeBounds (lb ub : ℤ) : ℕ → Bnd := fun i =>
  let len := max (bitsLen lb) (bitsLen ub)
  if i < len / 32 then ⟨if lb < 0 then 1 - 2 ^ 32 else 0, if 0 < ub then 2 ^ 32 - 1 else 0⟩
  else if i = len / 32 ∧ len % 32 ≠ 0 then
    ⟨lb / 2 ^ (len - len % 32), -((-ub) / 2 ^ (len - len % 32))⟩
  else Bnd.zero

/-- Bounds of a `Tight`-allocated element of the emulated field `[0, p₂ - 1]`. -/
def tightB (p2 : ℕ) : ℕ → Bnd := computeBounds 0 ((p2 : ℤ) - 1)

/-- Bounds of `from_bits_le` of `n` bits. -/
def bitsB (n : ℕ) : ℕ → Bnd := computeBounds 0 (2 ^ n - 1)

/-- The limbs of a canonical element as integers. -/
def limbZ (n : ℕ) (a : ℕ → ZMod p1) : ℕ → ℤ := fun i => if i < n then ((a i).val : ℤ) else 0

section Tight

variable (p2) (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (hp2 : (1 : ℤ) < p2)
include hbits hp2

theorem tightLen : max (bitsLen 0) (bitsLen ((p2 : ℤ) - 1)) = 254 := by
  simp [bitsLen, Nat.size_zero] at hbits ⊢; omega

theorem tightB_low {i : ℕ} (hi : i < 7) : tightB p2 i = ⟨0, 2 ^ 32 - 1⟩ := by
  have hlen := tightLen p2 hbits hp2
  simp only [tightB, computeBounds, hlen, show 254 / 32 = 7 by norm_num, hi, if_true]
  simp [hp2]

theorem tightB_top : tightB p2 7 = ⟨0, -((-((p2 : ℤ) - 1)) / 2 ^ 224)⟩ := by
  have hlen := tightLen p2 hbits hp2
  simp only [tightB, computeBounds, hlen, show 254 / 32 = 7 by norm_num,
    show 254 % 32 = 30 by norm_num, lt_irrefl, if_false, true_and, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, if_true]
  norm_num

theorem tightB_high {i : ℕ} (hi : 7 < i) : tightB p2 i = Bnd.zero := by
  have hlen := tightLen p2 hbits hp2
  simp only [tightB, computeBounds, hlen, show 254 / 32 = 7 by norm_num]
  rw [if_neg (by omega), if_neg (by omega)]

end Tight

/-- A canonical element (limbs `< 2^32`, value `< p₂`, `p₂` of 254 bits) is valid for the `Tight`
bounds. -/
theorem tight_valid (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {a : ℕ → ZMod p1}
    (h : Canon p2 a) : Valid (tightB p2) (tr 8 a) (limbZ 8 a) := by
  have hp2 : (1 : ℤ) < p2 := by
    have := (Fact.out : p2.Prime).two_le; omega
  intro i
  have hcast : tr 8 a i = ((limbZ 8 a i : ℤ) : ZMod p1) := by
    by_cases hi : i < 8
    · simp [tr, limbZ, hi]
    · simp [tr, limbZ, hi]
  refine ⟨?_, hcast⟩
  by_cases h7 : i < 7
  · rw [tightB_low p2 hbits hp2 h7]
    have := h.1 i (by omega)
    simp only [limbZ, show i < 8 by omega, if_true, Bnd.Mem]
    have : ((a i).val : ℤ) < 2 ^ 32 := by exact_mod_cast this
    exact ⟨by positivity, by omega⟩
  · by_cases h8 : i = 7
    · subst h8
      rw [tightB_top p2 hbits hp2]
      simp only [limbZ, show 7 < 8 by norm_num, if_true, Bnd.Mem]
      refine ⟨by positivity, ?_⟩
      have h1 : (a 7).val * 2 ^ (32 * 7) ≤ limbsVal 8 a := by
        unfold limbsVal
        rw [show (8 : ℕ) = 7 + 1 by norm_num, sum_range_succ]
        omega
      have h2 := h.2
      have hz : ((a 7).val : ℤ) * 2 ^ 224 ≤ (p2 : ℤ) - 1 := by
        have : ((a 7).val : ℤ) * 2 ^ (32 * 7) ≤ (limbsVal 8 a : ℤ) := by exact_mod_cast h1
        have h3 : (limbsVal 8 a : ℤ) < p2 := by exact_mod_cast h2
        norm_num at this ⊢
        omega
      have hd : (0 : ℤ) < 2 ^ 224 := by positivity
      have : (-((p2 : ℤ) - 1)) / 2 ^ 224 ≤ -((a 7).val : ℤ) := by
        have h5 : (-((p2 : ℤ) - 1)) / 2 ^ 224 < -((a 7).val : ℤ) + 1 :=
          (Int.ediv_lt_iff_lt_mul hd).mpr (by nlinarith)
        omega
      linarith
    · rw [tightB_high p2 hbits hp2 (by omega)]
      simp only [limbZ, show ¬ i < 8 by omega, if_false, Bnd.Mem, Bnd.zero]
      exact ⟨le_rfl, le_rfl⟩

/-! ### Loose allocation (`LimbedVar::alloc` with `RangeCheckMode::Loose`) -/

/-- Bounds of a loosely allocated variable of `n` limbs whose range has a negative lower bound
(`lbNeg`) and a positive upper bound (`ubPos`): only the bit length of each limb is enforced. -/
def looseB (lbNeg ubPos : Bool) (n : ℕ) : ℕ → Bnd := fun i =>
  if i < n then ⟨if lbNeg then 1 - 2 ^ 32 else 0, if ubPos then 2 ^ 32 - 1 else 0⟩ else Bnd.zero

/-- Constraints of a loose allocation: every absolute limb has 32 bits, the sign is a Boolean (or a
constant when the range has one sign), and `limb = neg ? -abs : abs`. -/
def LooseRel (lbNeg ubPos : Bool) (n : ℕ) (a : ℕ → ZMod p1) (neg : ZMod p1) : Prop :=
  ∃ (ab : ℕ → ZMod p1) (bits : ℕ → Fin 32 → ZMod p1),
    (∀ i < n, ToNBitsRel 32 (ab i) (bits i)) ∧
    (lbNeg = true → ubPos = true → IsBool neg) ∧
    (lbNeg = true → ubPos = false → neg = 1) ∧
    (lbNeg = false → neg = 0) ∧
    ∀ i < n, a i = ab i - 2 * neg * ab i

theorem loose_valid (hp1 : 2 ^ 32 ≤ p1) {lbNeg ubPos : Bool} {n : ℕ}
    (hne : 0 < n → lbNeg = true ∨ ubPos = true) {a : ℕ → ZMod p1} {neg : ZMod p1}
    (h : LooseRel lbNeg ubPos n a neg) :
    ∃ z : ℕ → ℤ, Valid (looseB lbNeg ubPos n) (tr n a) z := by
  obtain ⟨ab, bits, hb, h1, h2, h3, h4⟩ := h
  have hval : ∀ i < n, (ab i).val < 2 ^ 32 := fun i hi => (toNBits_sound hp1 (hb i hi)).2
  have hneg01 : neg = 0 ∨ neg = 1 := by
    by_cases hl : lbNeg = true
    · by_cases hu : ubPos = true
      · exact isBool_iff.mp (h1 hl hu)
      · exact Or.inr (h2 hl (by simpa using hu))
    · exact Or.inl (h3 (by simpa using hl))
  refine ⟨fun i => if i < n then (if neg = 1 then -((ab i).val : ℤ) else ((ab i).val : ℤ)) else 0, ?_⟩
  intro i
  by_cases hi : i < n
  · have hv := hval i hi
    have hv' : ((ab i).val : ℤ) < 2 ^ 32 := by exact_mod_cast hv
    refine ⟨?_, ?_⟩
    · simp only [looseB, hi, if_true, Bnd.Mem]
      rcases hneg01 with h0 | h0
      · subst h0
        have hl : lbNeg = false ∨ lbNeg = true := by cases lbNeg <;> simp
        have hu : ubPos = true := by
          rcases hne (by omega) with h | h
          · by_contra hu
            have hu' : ubPos = false := by simpa using hu
            have := h2 h hu'
            simp at this
          · exact h
        subst hu
        simp only [zero_ne_one, if_false]
        split_ifs <;> constructor <;> first | omega | positivity
      · subst h0
        have hl : lbNeg = true := by
          by_contra hl
          have hl' : lbNeg = false := by simpa using hl
          have := h3 hl'
          simp at this
        subst hl
        simp only [if_true]
        split_ifs <;> constructor <;> first | omega | positivity
    · simp only [tr, hi, if_true]
      rcases hneg01 with h0 | h0
      · subst h0; simp [h4 i hi]
      · subst h0; simp [h4 i hi]; ring
  · simp only [tr, hi, if_false, looseB, Bnd.Mem, Bnd.zero]
    exact ⟨⟨le_rfl, le_rfl⟩, by simp⟩

end Gadget
end Sonobe
