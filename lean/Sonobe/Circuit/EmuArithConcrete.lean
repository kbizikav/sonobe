import Sonobe.Circuit.FS2
import Sonobe.Circuit.Emulated.Modulo

/-!
**`EmuArith`, derived.** The two emulated operations of the secondary fold,
`(U.u + ρ).modulo()` and `(b * ρ + a).modulo()` (fs/nova/circuits/verifier.rs), as concrete
constraint predicates — `add_unaligned` / `mul_unaligned` followed by `modulo` — whose soundness
(`add_sound`, `mul_sound`) is proved from `modulo_sound`, `mulRel_sound` and the bounds algebra.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

theorem bitsLen_pow_sub_one (n : ℕ) : bitsLen ((2 : ℤ) ^ n - 1) = n := by
  unfold bitsLen
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h : ((2 : ℤ) ^ n - 1).natAbs = 2 ^ n - 1 := by
    have : ((2 : ℤ) ^ n - 1) = ((2 ^ n - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub h1]; ring
    rw [this, Int.natAbs_natCast]
  rw [h]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply le_antisymm
    · exact Nat.size_le.mpr (by omega)
    · have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      have h3 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      have : n - 1 < (2 ^ n - 1).size := Nat.lt_size.mpr (by omega)
      omega

/-- Bounds of `from_bits_le` of 128 bits: four full limbs. -/
theorem bitsLen_zero : bitsLen 0 = 0 := by simp [bitsLen]

theorem bitsB_len : max (bitsLen 0) (bitsLen ((2 : ℤ) ^ 128 - 1)) = 128 := by
  rw [bitsLen_pow_sub_one, bitsLen_zero]; simp

theorem bitsB_low {i : ℕ} (hi : i < 4) : bitsB 128 i = ⟨0, 2 ^ 32 - 1⟩ := by
  simp only [bitsB, computeBounds, bitsB_len, show 128 / 32 = 4 by norm_num, hi, if_true]
  have : (0 : ℤ) < 2 ^ 128 - 1 := by norm_num
  simp [this]

theorem bitsB_high {i : ℕ} (hi : 4 ≤ i) : bitsB 128 i = Bnd.zero := by
  simp only [bitsB, computeBounds, bitsB_len, show 128 / 32 = 4 by norm_num]
  rw [if_neg (by omega), if_neg (by simp)]

/-- A 128-bit challenge (four 32-bit limbs, zero past them) is valid for `from_bits_le`. -/
theorem bits_valid {b : ℕ → ZMod p1} (h1 : ∀ k < 4, (b k).val < 2 ^ 32)
    (h2 : ∀ k, 4 ≤ k → b k = 0) : Valid (bitsB 128) (tr 4 b) (limbZ 4 b) := by
  intro i
  by_cases hi : i < 4
  · rw [bitsB_low hi]
    have := h1 i hi
    have : ((b i).val : ℤ) < 2 ^ 32 := by exact_mod_cast this
    have e : limbZ 4 b i = ((b i).val : ℤ) := by simp only [limbZ, hi, if_true]
    refine ⟨⟨by show 0 ≤ limbZ 4 b i; rw [e]; positivity,
      by show limbZ 4 b i ≤ 2 ^ 32 - 1; rw [e]; omega⟩, by simp [limbZ, tr, hi]⟩
  · rw [bitsB_high (by omega)]
    simp [limbZ, tr, hi, Bnd.Mem, Bnd.zero]

theorem Bnd.mul_zero_left (b : Bnd) : Bnd.zero.mul b = Bnd.zero := by
  simp [Bnd.mul, Bnd.zero]

theorem Bnd.mul_zero_right (b : Bnd) : b.mul Bnd.zero = Bnd.zero := by
  simp [Bnd.mul, Bnd.zero]

theorem mulB_zero {bs cs : ℕ → Bnd} {n m : ℕ} (hb : ∀ i, n ≤ i → bs i = Bnd.zero)
    (hc : ∀ j, m ≤ j → cs j = Bnd.zero) {k : ℕ} (hk : n + m ≤ k + 1) : mulB bs cs k = Bnd.zero := by
  have h : ∀ i ∈ range (k + 1), (bs i).mul (cs (k - i)) = Bnd.zero := by
    intro i hi
    have hi' := mem_range.mp hi
    by_cases h1 : n ≤ i
    · rw [hb i h1, Bnd.mul_zero_left]
    · rw [hc (k - i) (by omega), Bnd.mul_zero_right]
  simp only [mulB]
  rw [sum_eq_zero fun i hi => by rw [h i hi]; rfl, sum_eq_zero fun i hi => by rw [h i hi]; rfl]
  rfl

/-- The shape of `U.u + ρ`. -/
def addShape (p2 : ℕ) : ModShape := ⟨addB (tightB p2) (bitsB 128), 8⟩

/-- The shape of `b * ρ + a`. -/
def mulShape (p2 : ℕ) : ModShape := ⟨addB (mulB (tightB p2) (bitsB 128)) (tightB p2), 11⟩

/-- `(a + ρ).modulo()`. -/
def ModAddC (p2 : ℕ) (a b o : ℕ → ZMod p1) : Prop :=
  ModRel p2 (addShape p2) (fun i => tr 8 a i + tr 4 b i) o

/-- `(a * ρ + c).modulo()`: the product limbs are hints pinned by the polynomial identity. -/
def ModMulAddC (p2 : ℕ) (a b c o : ℕ → ZMod p1) : Prop :=
  ∃ z, MulRel 8 4 a b z ∧ ModRel p2 (mulShape p2) (fun i => tr 11 z i + tr 8 c i) o

theorem emod_of_decomp {V Q R : ℤ} {m : ℤ} (h : V = Q * m + R) (h0 : 0 ≤ R) (h1 : R < m) :
    R = V % m := by
  rw [h, Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt h0 h1]

theorem tr_sum_idem (a b : ℕ → ZMod p1) (n m N : ℕ) (hn : n ≤ N) (hm : m ≤ N) :
    tr N (fun i => tr n a i + tr m b i) = fun i => tr n a i + tr m b i := by
  funext i
  by_cases hi : i < N
  · simp [tr, hi]
  · simp [tr, hi, show ¬ i < n by omega, show ¬ i < m by omega]

theorem addShape_zero (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (hp2 : (1 : ℤ) < p2) :
    ∀ i, (addShape p2).N ≤ i → (addShape p2).selfB i = Bnd.zero := by
  intro i hi
  have hi8 : 8 ≤ i := hi
  simp only [addShape, addB]
  rw [tightB_high p2 hbits hp2 (by omega), bitsB_high (by omega)]
  simp [Bnd.add, Bnd.zero]

theorem mulShape_zero (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (hp2 : (1 : ℤ) < p2) :
    ∀ i, (mulShape p2).N ≤ i → (mulShape p2).selfB i = Bnd.zero := by
  intro i hi
  have hi' : 11 ≤ i := hi
  simp only [mulShape, addB]
  rw [mulB_zero (n := 8) (m := 4) (fun j hj => tightB_high p2 hbits hp2 (by omega))
    (fun j hj => bitsB_high hj) (by omega), tightB_high p2 hbits hp2 (by omega)]
  simp [Bnd.add, Bnd.zero]

/-- Value of a canonical element. -/
theorem intVal_limbZ_eq (n : ℕ) (a : ℕ → ZMod p1) : intVal (limbZ n a) n = (limbsVal n a : ℤ) := by
  unfold intVal limbsVal
  push_cast
  refine sum_congr rfl fun i hi => ?_
  simp [limbZ, mem_range.mp hi]

theorem modAdd_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {a b o : ℕ → ZMod p1} (ha : Canon p2 a)
    (hb1 : ∀ k < 4, (b k).val < 2 ^ 32) (hb2 : ∀ k, 4 ≤ k → b k = 0) (h : ModAddC p2 a b o) :
    Canon p2 o ∧ limbsVal 8 o = (limbsVal 8 a + limbsVal 8 b) % p2 := by
  have hp2' : (1 : ℤ) < p2 := by have := (Fact.out : p2.Prime).two_le; omega
  have hS := valid_add (tight_valid hbits ha) (bits_valid hb1 hb2)
  unfold ModAddC at h
  have hS' : Valid (addShape p2).selfB (tr (addShape p2).N (fun i => tr 8 a i + tr 4 b i))
      (fun i => limbZ 8 a i + limbZ 4 b i) := by
    show Valid (addB (tightB p2) (bitsB 128)) (tr 8 (fun i => tr 8 a i + tr 4 b i)) _
    rw [tr_sum_idem a b 8 4 8 le_rfl (by norm_num)]
    exact hS
  obtain ⟨hcan, Q, hQ⟩ := modulo_sound hp hp2 (addShape p2) (addShape_zero hbits hp2') hS' h
  refine ⟨hcan, ?_⟩
  have hb8 : (limbsVal 4 b : ℤ) = (limbsVal 8 b : ℤ) := by
    unfold limbsVal
    rw [show (8 : ℕ) = 4 + 4 by norm_num, sum_range_add]
    have : ∀ i ∈ range 4, (b (4 + i)).val * 2 ^ (32 * (4 + i)) = 0 := fun i _ => by
      rw [hb2 (4 + i) (by omega)]; simp
    rw [sum_eq_zero this, add_zero]
  have hb4 : intVal (limbZ 4 b) 8 = intVal (limbZ 4 b) 4 :=
    intVal_eq_of_zero _ (by norm_num) fun i hi => by simp [limbZ, show ¬ i < 4 by omega]
  have hV : intVal (fun i => limbZ 8 a i + limbZ 4 b i) (addShape p2).N =
      (limbsVal 8 a : ℤ) + (limbsVal 8 b : ℤ) := by
    have e : (addShape p2).N = 8 := rfl
    rw [e, intVal_add, intVal_limbZ_eq 8 a, hb4, intVal_limbZ_eq 4 b, hb8]
  rw [hV] at hQ
  have hR := emod_of_decomp hQ (by positivity) (by exact_mod_cast hcan.2)
  have : ((limbsVal 8 o : ℕ) : ℤ) = (((limbsVal 8 a + limbsVal 8 b) % p2 : ℕ) : ℤ) := by
    rw [hR]; push_cast; rfl
  exact_mod_cast this

theorem conv_tr_zero (a b : ℕ → ZMod p1) {n m k : ℕ} (hk : n + m ≤ k + 1) :
    conv (tr n a) (tr m b) k = 0 := by
  unfold conv
  refine sum_eq_zero fun i hi => ?_
  have := mem_range.mp hi
  by_cases h : i < n
  · have : ¬ k - i < m := by omega
    simp [tr, this]
  · simp [tr, h]

theorem modMulAdd_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {a b c o : ℕ → ZMod p1} (ha : Canon p2 a)
    (hc : Canon p2 c) (hb1 : ∀ k < 4, (b k).val < 2 ^ 32) (hb2 : ∀ k, 4 ≤ k → b k = 0)
    (h : ModMulAddC p2 a b c o) :
    Canon p2 o ∧ limbsVal 8 o = (limbsVal 8 a * limbsVal 8 b + limbsVal 8 c) % p2 := by
  have hp2' : (1 : ℤ) < p2 := by have := (Fact.out : p2.Prime).two_le; omega
  have hp1' : 11 < p1 := by omega
  obtain ⟨z, hmul, hmod⟩ := h
  have hz := mulRel_sound (p := p1) (by norm_num) (by norm_num) (by simpa using hp1') hmul
  have hva := tight_valid hbits ha
  have hvb := bits_valid hb1 hb2
  have hvc := tight_valid hbits hc
  have hS := valid_add (valid_mul hva hvb) hvc
  have hfun : (fun i => tr 11 z i + tr 8 c i) =
      fun i => conv (tr 8 a) (tr 4 b) i + tr 8 c i := by
    funext i
    by_cases hi : i < 11
    · simp [tr, hi, hz i (by simpa using hi)]
    · simp [tr, hi, conv_tr_zero a b (by omega : 8 + 4 ≤ i + 1), show ¬ i < 8 by omega]
  have hself : tr 11 (fun i => tr 11 z i + tr 8 c i) =
      fun i => conv (tr 8 a) (tr 4 b) i + tr 8 c i := by
    rw [hfun]
    funext i
    by_cases hi : i < 11
    · simp [tr, hi]
    · simp [tr, hi, conv_tr_zero a b (by omega : 8 + 4 ≤ i + 1), show ¬ i < 8 by omega]
  have hS' : Valid (mulShape p2).selfB (tr (mulShape p2).N (fun i => tr 11 z i + tr 8 c i))
      (fun i => conv (limbZ 8 a) (limbZ 4 b) i + limbZ 8 c i) := by
    show Valid (addB (mulB (tightB p2) (bitsB 128)) (tightB p2)) (tr 11 _) _
    rw [hself]; exact hS
  obtain ⟨hcan, Q, hQ⟩ := modulo_sound hp hp2 (mulShape p2) (mulShape_zero hbits hp2') hS' hmod
  refine ⟨hcan, ?_⟩
  have hb8 : (limbsVal 4 b : ℤ) = (limbsVal 8 b : ℤ) := by
    unfold limbsVal
    rw [show (8 : ℕ) = 4 + 4 by norm_num, sum_range_add]
    have : ∀ i ∈ range 4, (b (4 + i)).val * 2 ^ (32 * (4 + i)) = 0 := fun i _ => by
      rw [hb2 (4 + i) (by omega)]; simp
    rw [sum_eq_zero this, add_zero]
  have hV : intVal (fun i => conv (limbZ 8 a) (limbZ 4 b) i + limbZ 8 c i) (mulShape p2).N =
      (limbsVal 8 a : ℤ) * (limbsVal 8 b : ℤ) + (limbsVal 8 c : ℤ) := by
    have e : (mulShape p2).N = 11 := rfl
    rw [e, intVal_add]
    have hza : ∀ i, 8 ≤ i → limbZ 8 a i = 0 := fun i hi => by simp [limbZ, show ¬ i < 8 by omega]
    have hzb : ∀ i, 4 ≤ i → limbZ 4 b i = 0 := fun i hi => by simp [limbZ, show ¬ i < 4 by omega]
    rw [intVal_conv hza hzb (by norm_num : 8 + 4 ≤ 11 + 1), intVal_limbZ_eq 8 a,
      intVal_limbZ_eq 4 b, hb8,
      intVal_eq_of_zero _ (by norm_num : 8 ≤ 11) (fun i hi => by simp [limbZ, show ¬ i < 8 by omega]),
      intVal_limbZ_eq 8 c]
  rw [hV] at hQ
  have h0 : (0 : ℤ) ≤ (limbsVal 8 o : ℤ) := Int.natCast_nonneg _
  have h1 : (limbsVal 8 o : ℤ) < (p2 : ℤ) := by exact_mod_cast hcan.2
  have hR := emod_of_decomp hQ h0 h1
  have : ((limbsVal 8 o : ℕ) : ℤ) =
      (((limbsVal 8 a * limbsVal 8 b + limbsVal 8 c) % p2 : ℕ) : ℤ) := by
    rw [hR]; push_cast; rfl
  exact_mod_cast this

/-- The emulated arithmetic of the secondary fold, with `ModAdd`/`ModMulAdd` the concrete
constraint predicates and soundness proved (not assumed). -/
def EmuArith.concrete (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) : EmuArith p1 p2 where
  ModAdd := ModAddC p2
  ModMulAdd := ModMulAddC p2
  add_sound a b o ha hb1 hb2 h := modAdd_sound hp hp2 hbits ha hb1 hb2 h
  mul_sound a b c o ha hc hb1 hb2 h := modMulAdd_sound hp hp2 hbits ha hc hb1 hb2 h

end Gadget
end Sonobe
