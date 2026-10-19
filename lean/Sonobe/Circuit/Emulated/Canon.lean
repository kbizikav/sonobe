import Sonobe.Circuit.Emulated.Absorb

/-!
Canonical emulated values: a `Tight` allocation of an element of `E = ZMod p2` inside a circuit
over `F = ZMod p1` yields eight 32-bit limbs whose value is `< p2`.
-/

namespace Sonobe
namespace Gadget

open Finset

/-- Limb `i` of `m` in base `2^32`. -/
def mlimb (m i : ℕ) : ℕ := (m / 2 ^ (32 * i)) % 2 ^ 32

theorem sum_mlimb (m : ℕ) : ∀ N, ∑ i ∈ range N, mlimb m i * 2 ^ (32 * i) = m % 2 ^ (32 * N)
  | 0 => by simp [Nat.mod_one]
  | N + 1 => by
    rw [sum_range_succ, sum_mlimb m N, show 32 * (N + 1) = 32 * N + 32 by ring, pow_add,
      Nat.mod_mul]
    unfold mlimb; ring

variable {p1 p2 : ℕ} [Fact p1.Prime]

/-- Canonical eight-limb representation of a value below `p2`. -/
def Canon (p2 : ℕ) (a : ℕ → ZMod p1) : Prop :=
  (∀ i < 8, (a i).val < 2 ^ 32) ∧ limbsVal 8 a < p2

/-- The emulated element represented by the limbs. -/
def emuV (p2 : ℕ) (a : ℕ → ZMod p1) : ZMod p2 := ((limbsVal 8 a : ℕ) : ZMod p2)

theorem mlimb_lt (m i : ℕ) : mlimb m i < 2 ^ 32 := Nat.mod_lt _ (by positivity)

/-- A tight allocation (against the limbs of `p2 < 2^256`) is canonical. -/
theorem tight_canon [Fact p2.Prime] (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    {a : ℕ → ZMod p1} {w : TightWit p1 8 32} (h : TightRel 8 32 (mlimb p2) a w) :
    Canon p2 a := by
  have h8 : (8 : ℕ) < p1 := by
    have := (Fact.out : p1.Prime).two_le; omega
  have := tight_sound (p := p1) (N := 8) (nb := 32) h8 (by omega) (fun i _ => mlimb_lt p2 i) h
  refine ⟨this.1, ?_⟩
  have e := sum_mlimb p2 8
  rw [Nat.mod_eq_of_lt hp2] at e
  have h2 : ∑ i ∈ range 8, mlimb p2 i * 2 ^ (32 * i) = p2 := e
  simpa [h2] using this.2

omit [Fact (Nat.Prime p1)] in
theorem emuV_val [Fact p2.Prime] {a : ℕ → ZMod p1} (h : Canon p2 a) :
    (emuV p2 a).val = limbsVal 8 a := ZMod.val_natCast_of_lt h.2

end Gadget
end Sonobe
