import Sonobe.Circuit.Emulated.Limbs
import Sonobe.Circuit.Emulated.Lt

/-!
`LimbedVar::enforce_equal_unaligned` (primitives/src/algebra/field/emulated.rs): the equality of
two unaligned limbed integers, as a carry chain over groups of limbs.

The static part — grouping of the limbs and the range check of the carry that closes each group —
depends on the bounds only; `run` is its transcription (with `Option` for the synthesis-time
failures). The circuit part is a field carry `C_{i+1} = (C_i + d_i) / 2^32` that is range-checked at
the end of every group and must vanish at the end.

**Soundness**: if the plan succeeds, the limbs are within their bounds and the carry constraints
hold, then `Σ z_i 2^(32 i) = 0` over `ℤ`.
-/

namespace Sonobe
namespace Gadget

open Finset

/-- A range-checked carry: before limb `idx`, `carry - lb` has `nb` bits; it closes a group of
`k` limbs. -/
structure Ev where
  idx : ℕ
  lb : ℤ
  nb : ℕ
  k : ℕ

/-- Closing a group of `len` limbs whose value lies in `vb` (`LimbedVar::carry_range`): the lower
bound `lb` of the carry, the number of bits `nb` of `carry - lb` and the range `[lb, lb + 2^nb - 1]`
it allows. Fails unless `carry * 2^(32 len) - v` is below the field size `M` in absolute value for
all values of the range. -/
def carryRange (M : ℤ) (vb : Bnd) (len : ℕ) : Option (ℤ × ℕ × Bnd) :=
  let tight := vb.shrN (32 * len)
  if tight.hi < tight.lo then none else
  let nb := (tight.hi - tight.lo + 1).toNat.size
  let range : Bnd := ⟨tight.lo, tight.lo + 2 ^ nb - 1⟩
  let sc := range.shl (32 * len)
  if sc.lo - vb.hi ≤ -M ∨ M ≤ sc.hi - vb.lo then none else some (tight.lo, nb, range)

/-- Process one limb with bounds `B`. -/
def step (L M : ℤ) (vb : Bnd) (len : ℕ) (B : Bnd) : Option (Bnd × ℕ × Option (ℤ × ℕ × ℕ)) :=
  match (vb.add (B.shl (32 * len))).filterSafe L with
  | some e => some (e, len + 1, none)
  | none => do
    let (lb, nb, range) ← carryRange M vb len
    let vb' ← (range.add B).filterSafe L
    some (vb', 1, some (lb, nb, len))

/-- The plan of the first `i` limbs: bounds of the current group, its length and the events. -/
def run (L M : ℤ) (bs : ℕ → Bnd) : ℕ → Option (Bnd × ℕ × List Ev)
  | 0 => some (Bnd.zero, 0, [])
  | i + 1 => do
    let (vb, len, evs) ← run L M bs i
    let (vb', len', ev) ← step L M vb len (bs i)
    some (vb', len', evs ++ (ev.map fun e => (⟨i, e.1, e.2.1, e.2.2⟩ : Ev)).toList)

variable {p : ℕ} [Fact p.Prime]

/-- The field carry `C_{i+1} = (C_i + d_i) / 2^32`. -/
noncomputable def carryF (d : ℕ → ZMod p) : ℕ → ZMod p
  | 0 => 0
  | i + 1 => (carryF d i + d i) * ((2 : ZMod p) ^ 32)⁻¹

/-- The constraints: every closing carry is in its checked range, the last carry is zero. -/
def EqRel (d : ℕ → ZMod p) (n : ℕ) (evs : List Ev) : Prop :=
  (∀ e ∈ evs, ∃ t : ℤ, e.lb ≤ t ∧ t ≤ e.lb + 2 ^ e.nb - 1 ∧ carryF d e.idx = (t : ZMod p)) ∧
    carryF d n = 0

/-- Value of the limbs `[s, i)` relative to `s`. -/
def grpVal (z : ℕ → ℤ) (s i : ℕ) : ℤ := ∑ j ∈ Ico s i, z j * 2 ^ (32 * (j - s))

theorem grpVal_succ (z : ℕ → ℤ) {s i : ℕ} (h : s ≤ i) :
    grpVal z s (i + 1) = grpVal z s i + z i * 2 ^ (32 * (i - s)) := by
  unfold grpVal; rw [sum_Ico_succ_top h]

theorem intVal_split (z : ℕ → ℤ) {s i : ℕ} (h : s ≤ i) :
    intVal z i = intVal z s + 2 ^ (32 * s) * grpVal z s i := by
  unfold intVal grpVal
  rw [← sum_range_add_sum_Ico _ h, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have := (mem_Ico.mp hj).1
  rw [show 32 * j = 32 * s + 32 * (j - s) by omega, pow_add]; ring

theorem int_eq_of_cast {D : ℤ} (hD : |D| < p) (h : (D : ZMod p) = 0) : D = 0 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mp h
  exact Int.eq_zero_of_abs_lt_dvd this hD

/-- The invariant after `i` limbs. -/
def Inv (L : ℤ) (z : ℕ → ℤ) (d : ℕ → ZMod p) (i : ℕ) (vb : Bnd) (len : ℕ) : Prop :=
  len ≤ i ∧ Bnd.Safe L vb ∧
    ∃ c : ℤ, intVal z (i - len) = c * 2 ^ (32 * (i - len)) ∧
      Bnd.Mem (c + grpVal z (i - len) i) vb ∧
      carryF d i * (2 : ZMod p) ^ (32 * len) = ((c + grpVal z (i - len) i : ℤ) : ZMod p)

/-- The event part of the constraints. -/
def EvRel (d : ℕ → ZMod p) (evs : List Ev) : Prop :=
  ∀ e ∈ evs, ∃ t : ℤ, e.lb ≤ t ∧ t ≤ e.lb + 2 ^ e.nb - 1 ∧ carryF d e.idx = (t : ZMod p)

theorem Bnd.filterSafe_eq_some {L : ℤ} {a b : Bnd} : a.filterSafe L = some b ↔ Bnd.Safe L a ∧ a = b := by
  unfold Bnd.filterSafe
  split_ifs with h <;> simp [h]

theorem carryRange_spec {M : ℤ} {vb : Bnd} {len : ℕ} {lb : ℤ} {nb : ℕ} {range : Bnd}
    (h : carryRange M vb len = some (lb, nb, range)) :
    range = ⟨lb, lb + 2 ^ nb - 1⟩ ∧ -M < lb * 2 ^ (32 * len) - vb.hi ∧
      (lb + 2 ^ nb - 1) * 2 ^ (32 * len) - vb.lo < M := by
  unfold carryRange at h
  simp only at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨rfl, ?_, ?_⟩
  · simp only [Bnd.shl, not_or, not_le] at h2
    simpa using h2.1
  · simp only [Bnd.shl, not_or, not_le] at h2
    simpa using h2.2

theorem inv_all (hp : 2 ^ 32 < p) {bs : ℕ → Bnd} {z : ℕ → ℤ} {d : ℕ → ZMod p}
    (hL : (0 : ℤ) ≤ ((p : ℤ) - 1) / 2) (hz : ∀ i, Bnd.Mem (z i) (bs i))
    (hd : ∀ i, d i = (z i : ZMod p)) :
    ∀ (n : ℕ) {vb len evs}, run (((p : ℤ) - 1) / 2) p bs n = some (vb, len, evs) →
      EvRel d evs → Inv (((p : ℤ) - 1) / 2) z d n vb len := by
  have h2 : (2 : ZMod p) ^ 32 ≠ 0 := by
    intro h0
    have : ((2 ^ 32 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact h0
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp this
    have := Nat.le_of_dvd (by positivity) hdvd
    omega
  have hinv : ((2 : ZMod p) ^ 32)⁻¹ * (2 : ZMod p) ^ 32 = 1 := inv_mul_cancel₀ h2
  intro n
  induction n with
  | zero =>
    intro vb len evs h _
    simp only [run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨le_rfl, ⟨?_, ?_, ?_⟩, 0, ?_, ?_, ?_⟩
    · simp [Bnd.zero]; omega
    · simp [Bnd.zero]; omega
    · simp [Bnd.zero]; omega
    · simp [intVal]
    · simp [grpVal, Bnd.Mem, Bnd.zero]
    · simp [carryF, grpVal]
  | succ n ih =>
    intro vb len evs h hev
    simp only [run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨vb0, len0, evs0⟩, h0, ⟨vb1, len1, ev⟩, h1, h2'⟩ := h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2'
    obtain ⟨rfl, rfl, rfl⟩ := h2'
    have hev0 : EvRel d evs0 := fun e he => hev e (List.mem_append_left _ he)
    obtain ⟨hlen, hsafe, c, hb, hmem, hcar⟩ := ih h0 hev0
    set s := n - len0 with hs
    have hsn : s + len0 = n := by omega
    have hnum : n - s = len0 := by omega
    unfold step at h1
    split at h1
    · -- the group is extended
      rename_i e he
      obtain ⟨hsafe', rfl⟩ := Bnd.filterSafe_eq_some.mp he
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      have e1 : n + 1 - (len0 + 1) = s := by omega
      refine ⟨by omega, hsafe', c, ?_, ?_, ?_⟩
      · rw [e1]; exact hb
      · rw [e1, grpVal_succ z (by omega : s ≤ n), hnum, ← add_assoc]
        exact Bnd.mem_add hmem (Bnd.mem_shl (hz n) _)
      · rw [e1, grpVal_succ z (by omega : s ≤ n), hnum]
        push_cast
        have e : (2 : ZMod p) ^ (32 * (len0 + 1)) = 2 ^ (32 * len0) * 2 ^ 32 := by
          rw [Nat.mul_succ, pow_add]
        have hcar' := hcar
        push_cast at hcar'
        rw [carryF, e, hd n]
        linear_combination hcar' + ((carryF d n + (z n : ZMod p)) * 2 ^ (32 * len0)) * hinv
    · -- the group is closed
      rename_i hnone
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h1
      obtain ⟨⟨lb, nb, range⟩, hcr, vb', hfs, hres⟩ := h1
      simp only [Option.some.injEq, Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl, rfl⟩ := hres
      obtain ⟨hrange, hlow, hup⟩ := carryRange_spec hcr
      obtain ⟨hsafe', hvb'⟩ := Bnd.filterSafe_eq_some.mp hfs
      obtain ⟨t, htlo, htup, hct⟩ := hev ⟨n, lb, nb, len0⟩ (by simp)
      have hmem' := hmem
      obtain ⟨hm1, hm2⟩ := hmem'
      -- `t * 2^(32 len0) = c + G` over `ℤ`
      have hD : ((t * 2 ^ (32 * len0) - (c + grpVal z s n) : ℤ) : ZMod p) = 0 := by
        push_cast
        have hcar' := hcar
        push_cast at hcar'
        rw [hct] at hcar'
        rw [hcar']; ring
      have hbd : |t * 2 ^ (32 * len0) - (c + grpVal z s n)| < p := by
        have hpos : (0 : ℤ) < 2 ^ (32 * len0) := by positivity
        have l1 : lb * 2 ^ (32 * len0) ≤ t * 2 ^ (32 * len0) :=
          Int.mul_le_mul_of_nonneg_right htlo hpos.le
        have l2 : t * 2 ^ (32 * len0) ≤ (lb + 2 ^ nb - 1) * 2 ^ (32 * len0) :=
          Int.mul_le_mul_of_nonneg_right (by linarith) hpos.le
        rw [abs_lt]; constructor <;> linarith
      have hD0 := int_eq_of_cast hbd hD
      have hV : c + grpVal z s n = t * 2 ^ (32 * len0) := by linarith
      refine ⟨by omega, by rw [← hvb']; exact hsafe', t, ?_, ?_, ?_⟩
      · have e1 : n + 1 - 1 = n := by omega
        rw [e1, intVal_split z (by omega : s ≤ n), hb]
        have : (2 : ℤ) ^ (32 * n) = 2 ^ (32 * s) * 2 ^ (32 * len0) := by rw [← pow_add]; congr 1; omega
        rw [this]; linear_combination (2 ^ (32 * s) : ℤ) * hV
      · have e1 : n + 1 - 1 = n := by omega
        rw [e1, ← hvb']
        have : grpVal z n (n + 1) = z n := by simp [grpVal]
        rw [this]
        exact Bnd.mem_add (by rw [hrange]; exact ⟨htlo, htup⟩) (hz n)
      · have e1 : n + 1 - 1 = n := by omega
        have : grpVal z n (n + 1) = z n := by simp [grpVal]
        rw [e1, this]
        push_cast
        rw [carryF, hct, hd n]
        have e : (2 : ZMod p) ^ (32 * 1) = 2 ^ 32 := by norm_num
        rw [e]
        linear_combination ((t : ZMod p) + z n) * hinv

/-- **`enforce_equal_unaligned` is sound.** If the plan succeeds for the static bounds, the limbs
(images of integers `z i ∈ bs i`) satisfy the carry constraints, then their integer value is `0`. -/
theorem eq_unaligned_sound (hp : 2 ^ 32 < p) (hLp : ((p : ℤ) - 1) / 2 < p) {bs : ℕ → Bnd}
    {z : ℕ → ℤ} {d : ℕ → ZMod p} (hz : ∀ i, Bnd.Mem (z i) (bs i)) (hd : ∀ i, d i = (z i : ZMod p))
    {n : ℕ} {vb : Bnd} {len : ℕ} {evs : List Ev}
    (hrun : run (((p : ℤ) - 1) / 2) p bs n = some (vb, len, evs)) (hc : EqRel d n evs) :
    intVal z n = 0 := by
  have hL : (0 : ℤ) ≤ ((p : ℤ) - 1) / 2 := by
    have : (1 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    omega
  obtain ⟨hlen, hsafe, c, hb, hmem, hcar⟩ := inv_all hp hL hz hd n hrun hc.1
  have h2 : (2 : ZMod p) ^ 32 ≠ 0 := by
    intro h0
    have : ((2 ^ 32 : ℕ) : ZMod p) = 0 := by rw [Nat.cast_pow, Nat.cast_ofNat]; exact h0
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp this
    have := Nat.le_of_dvd (by positivity) hdvd
    omega
  have h0 : ((c + grpVal z (n - len) n : ℤ) : ZMod p) = 0 := by
    rw [← hcar, hc.2, zero_mul]
  have hbd : |c + grpVal z (n - len) n| < p := by
    obtain ⟨h1, h2', h3⟩ := hsafe
    obtain ⟨m1, m2⟩ := hmem
    rw [abs_lt]; constructor <;> linarith
  have hV := int_eq_of_cast hbd h0
  rw [intVal_split z (by omega : n - len ≤ n), hb]
  linear_combination (2 ^ (32 * (n - len)) : ℤ) * hV

end Gadget
end Sonobe
