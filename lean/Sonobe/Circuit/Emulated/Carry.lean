import Sonobe.Circuit.Emulated.Alloc

/-!
`LimbedVar::enforce_equal_unaligned` (primitives/src/algebra/field/emulated.rs:636-725).

The Rust code walks over the difference limbs `d_i` (field elements, integer-valued with known
static magnitude), keeping a *field* carry `c ← (c + d_i)/2^32`. A group of limbs is closed by a
"flush" which range-checks the carry (so it is a small integer); the last carry must be `0`.

This file proves the integer lifting: if the carry at each group boundary is an integer `c_t`
(`c_0 = 0`, `c_g = 0`), the field congruences hold per group, and the integers involved stay below
`p`, then `Σ δ_i 2^(32 i) = 0` over `ℤ`.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- Value of the limbs `[a, b)` of a group, relative to its first limb. -/
def grp (δ : ℕ → ℤ) (a b : ℕ) : ℤ := ∑ i ∈ Ico a b, δ i * 2 ^ (32 * (i - a))

theorem sum_range_groups (δ : ℕ → ℤ) (s : ℕ → ℕ) (hs : ∀ t, s t ≤ s (t + 1)) (hs0 : s 0 = 0) :
    ∀ g, ∑ i ∈ range (s g), δ i * 2 ^ (32 * i) =
      ∑ t ∈ range g, 2 ^ (32 * s t) * grp δ (s t) (s (t + 1))
  | 0 => by simp [hs0]
  | g + 1 => by
    rw [sum_range_succ, ← sum_range_groups δ s hs hs0 g,
      ← sum_range_add_sum_Ico _ (hs g)]
    congr 1
    unfold grp
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have := (mem_Ico.mp hi).1
    rw [show 32 * i = 32 * s g + 32 * (i - s g) by omega, pow_add]; ring

/-- Integer lifting of the carry chain. -/
theorem carry_lift {g : ℕ} (δ : ℕ → ℤ) (s : ℕ → ℕ) (hs : ∀ t, s t ≤ s (t + 1)) (hs0 : s 0 = 0)
    (c : ℕ → ℤ) (hc0 : c 0 = 0) (hcg : c g = 0)
    (hcong : ∀ t < g, (((grp δ (s t) (s (t + 1)) + c t : ℤ)) : ZMod p) =
      (((c (t + 1) * 2 ^ (32 * (s (t + 1) - s t)) : ℤ)) : ZMod p))
    (hbound : ∀ t < g, |grp δ (s t) (s (t + 1)) + c t - c (t + 1) * 2 ^ (32 * (s (t + 1) - s t))|
      < p) :
    ∑ i ∈ range (s g), δ i * 2 ^ (32 * i) = 0 := by
  have hgroup : ∀ t < g, grp δ (s t) (s (t + 1)) + c t = c (t + 1) * 2 ^ (32 * (s (t + 1) - s t)) := by
    intro t ht
    have h0 : ((grp δ (s t) (s (t + 1)) + c t - c (t + 1) * 2 ^ (32 * (s (t + 1) - s t)) : ℤ) :
        ZMod p) = 0 := by
      push_cast at hcong ⊢
      rw [sub_eq_zero]; exact hcong t ht
    have := int_eq_zero_of_cast (hbound t ht) h0
    linarith
  rw [sum_range_groups δ s hs hs0]
  have key : ∀ t < g, 2 ^ (32 * s t) * grp δ (s t) (s (t + 1)) =
      c (t + 1) * 2 ^ (32 * s (t + 1)) - c t * 2 ^ (32 * s t) := by
    intro t ht
    have e := hgroup t ht
    have hsplit : (2 : ℤ) ^ (32 * s (t + 1)) = 2 ^ (32 * s t) * 2 ^ (32 * (s (t + 1) - s t)) := by
      rw [← pow_add]; congr 1; have := hs t; omega
    rw [hsplit]
    have : grp δ (s t) (s (t + 1)) = c (t + 1) * 2 ^ (32 * (s (t + 1) - s t)) - c t := by linarith
    rw [this]; ring
  have htele : ∀ n ≤ g, ∑ t ∈ range n, 2 ^ (32 * s t) * grp δ (s t) (s (t + 1)) =
      c n * 2 ^ (32 * s n) - c 0 * 2 ^ (32 * s 0) := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih (by omega), key n (by omega)]; ring
  rw [htele g le_rfl, hcg, hc0]; simp

end Gadget
end Sonobe
