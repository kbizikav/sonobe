import Sonobe.Circuit.Emulated.Lt

/-!
Emulated field elements: `Tight` allocation (primitives/src/algebra/field/emulated.rs:280-362).

`N = 8` limbs of 32 bits (BN254/Grumpkin, 254-bit modulus `m`): every limb passes
`enforce_bit_length(32)` and the whole value passes `enforce_lt(m)`. The represented value is
`Σ limb_i · 2^(32 i)`; `Tight` allocation makes it the canonical representative in `[0, m)`.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Value of the limb vector. -/
def limbsVal (N : ℕ) (a : ℕ → ZMod p) : ℕ := ∑ i ∈ range N, (a i).val * 2 ^ (32 * i)

/-- Bits and `enforce_lt` witnesses of one tight allocation. -/
structure TightWit (p : ℕ) (N nb : ℕ) where
  limbBits : ℕ → Fin 32 → ZMod p
  b : ℕ → ZMod p
  pb : Fin nb → ZMod p

/-- `LimbedVar::alloc(.., Tight)` for a non-negative value below the constant `m` (given by its
32-bit limbs `c`). -/
def TightRel (N nb : ℕ) (c : ℕ → ℕ) (a : ℕ → ZMod p) (w : TightWit p N nb) : Prop :=
  (∀ i < N, ToNBitsRel 32 (a i) (w.limbBits i)) ∧ LtRel N nb a c w.b w.pb

/-- **Tight allocation is canonical**: limbs are 32-bit and the value is `< m`. -/
theorem tight_sound {N nb : ℕ} (hN : N < p) (hp : 2 ^ nb + 2 ^ 33 < p) {c : ℕ → ℕ}
    (hc : ∀ i < N, c i < 2 ^ 32) {a : ℕ → ZMod p} {w : TightWit p N nb}
    (h : TightRel N nb c a w) :
    (∀ i < N, (a i).val < 2 ^ 32) ∧ limbsVal N a < ∑ i ∈ range N, c i * 2 ^ (32 * i) := by
  obtain ⟨hbits, hlt⟩ := h
  have h32 : 2 ^ 32 ≤ p := by
    have : 2 ^ 33 < p := lt_of_le_of_lt (Nat.le_add_left _ _) hp
    have : 2 ^ 32 ≤ 2 ^ 33 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hlimb : ∀ i < N, (a i).val < 2 ^ 32 := fun i hi => (toNBits_sound h32 (hbits i hi)).2
  exact ⟨hlimb, lt_sound hN hp hlimb hc hlt⟩

end Gadget
end Sonobe
