import Sonobe.Circuit.Emulated.Alloc

/-!
`AbsorbableVar` for an emulated field variable (primitives/src/algebra/field/emulated.rs:1011-1036):
`to_bits_le` concatenates, limb by limb, `limb.to_n_bits_le(bound.hi.bits())` — 32 bits for the
low limbs and `tb` bits for the top limb (30 for BN254/Grumpkin moduli) — and the bits are packed
into chunks of `MODULUS_BIT_SIZE - 1 = 253` bits with `le_bits_to_fp`.

For a 254-bit value `V` this absorbs exactly `[V mod 2^253, V / 2^253]`, the native encoding.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p : ℕ} [Fact p.Prime]

theorem natVal_add (f : ℕ → Bool) (n m : ℕ) :
    natVal (n + m) f = natVal n f + 2 ^ n * natVal m (fun j => f (n + j)) := by
  unfold natVal
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [pow_add]; split_ifs <;> ring

/-- Bit `j` of the concatenation of 7 limbs of 32 bits and a top limb of `tb` bits. -/
def catBit (bl : ℕ → ℕ → Bool) (bt : ℕ → Bool) (j : ℕ) : Bool :=
  if j < 224 then bl (j / 32) (j % 32) else bt (j - 224)

theorem natVal_cat (bl : ℕ → ℕ → Bool) (bt : ℕ → Bool) :
    ∀ k ≤ 7, natVal (32 * k) (catBit bl bt) = ∑ i ∈ range k, natVal 32 (bl i) * 2 ^ (32 * i)
  | 0, _ => by simp [natVal]
  | k + 1, hk => by
    rw [sum_range_succ, ← natVal_cat bl bt k (by omega), show 32 * (k + 1) = 32 * k + 32 by ring,
      natVal_add]
    have : natVal 32 (fun j => catBit bl bt (32 * k + j)) = natVal 32 (bl k) := by
      unfold natVal
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      have h1 : 32 * k + j < 224 := by omega
      have h2 : (32 * k + j) / 32 = k := by omega
      have h3 : (32 * k + j) % 32 = j := by omega
      simp [catBit, h1, h2, h3]
    rw [this]; ring

/-- Bits of the eight limbs. -/
structure AbsWit (p : ℕ) where
  bl : ℕ → Fin 32 → ZMod p
  bt : Fin 30 → ZMod p

/-- The two absorbed field elements. -/
def EmuAbsRel (a : ℕ → ZMod p) (w : AbsWit p) (out : ZMod p × ZMod p) : Prop :=
  (∀ i < 7, ToNBitsRel 32 (a i) (w.bl i)) ∧ ToNBitsRel 30 (a 7) w.bt ∧
    out.1 = ∑ j ∈ range 253, (if catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) j then 1 else 0) * 2 ^ j ∧
    out.2 = if catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) 253 then 1 else 0

/-- Generic arithmetic of the repacking: `V = c₀ + 2^253 c₁` with `c₀ < 2^253`, `c₁ < 2`. -/
theorem divmod_of_split {V c0 c1 : ℕ} (h : V = c0 + 2 ^ 253 * c1) (h0 : c0 < 2 ^ 253) :
    V % 2 ^ 253 = c0 ∧ V / 2 ^ 253 = c1 := by
  subst h
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, zero_add]

/-- **Absorbing an emulated variable is the native encoding.** -/
theorem emuAbs_sound (h32 : 2 ^ 32 ≤ p) {a : ℕ → ZMod p} {w : AbsWit p} {out : ZMod p × ZMod p}
    (h : EmuAbsRel a w out) :
    out.1 = (((limbsVal 8 a) % 2 ^ 253 : ℕ) : ZMod p) ∧
      out.2 = (((limbsVal 8 a) / 2 ^ 253 : ℕ) : ZMod p) := by
  obtain ⟨hl, ht, ho1, ho2⟩ := h
  generalize hg : catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) = g at ho1 ho2
  have hL : ∀ i < 7, natVal 32 (fun t => bitsOf (w.bl i) t) = (a i).val := fun i hi =>
    ((toNBits_sound h32 (hl i hi)).1).symm
  have hT : natVal 30 (bitsOf w.bt) = (a 7).val := by
    have h30 : 2 ^ 30 ≤ p := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h32
    exact ((toNBits_sound h30 ht).1).symm
  have e1 : natVal 224 g = ∑ i ∈ range 7, natVal 32 (fun t => bitsOf (w.bl i) t) * 2 ^ (32 * i) := by
    have := natVal_cat (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) 7 le_rfl
    rw [hg] at this
    simpa only [Nat.reduceMul] using this
  have e2 : natVal (224 + 30) g = natVal 224 g + 2 ^ 224 * natVal 30 (fun j => g (224 + j)) :=
    natVal_add g 224 30
  have e3 : natVal 30 (fun j => g (224 + j)) = natVal 30 (bitsOf w.bt) := by
    unfold natVal
    refine sum_congr rfl fun j hj => ?_
    have : ¬ (224 + j < 224) := by omega
    simp [← hg, catBit, this]
  have hV : limbsVal 8 a = natVal (253 + 1) g := by
    have e5 : natVal (253 + 1) g = natVal (224 + 30) g := by simp only [Nat.reduceAdd]
    rw [e5, e2, e3, e1, hT]
    unfold limbsVal
    rw [show (8 : ℕ) = 7 + 1 by norm_num, sum_range_succ]
    have hs : ∑ i ∈ range 7, natVal 32 (fun t => bitsOf (w.bl i) t) * 2 ^ (32 * i) =
        ∑ i ∈ range 7, (a i).val * 2 ^ (32 * i) :=
      sum_congr rfl fun i hi => by rw [hL i (mem_range.mp hi)]
    rw [hs]
    norm_num
    ring
  have hsplit : natVal (253 + 1) g = natVal 253 g + 2 ^ 253 * natVal 1 (fun j => g (253 + j)) :=
    natVal_add g 253 1
  have hone : natVal 1 (fun j => g (253 + j)) = if g 253 then 1 else 0 := by
    simp [natVal]
  have hc0 : natVal 253 g < 2 ^ 253 := natVal_lt _ _
  have hc1 : (if g 253 then 1 else 0 : ℕ) < 2 := by split_ifs <;> norm_num
  obtain ⟨hmod, hdiv⟩ := divmod_of_split (hV.trans (hsplit.trans (by rw [hone]))) hc0
  refine ⟨?_, ?_⟩
  · rw [hmod, ho1]
    unfold natVal
    push_cast
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · rw [hdiv, ho2]
    split_ifs <;> simp

end Gadget
end Sonobe
