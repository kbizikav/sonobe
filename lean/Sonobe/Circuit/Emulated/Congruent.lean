import Sonobe.Circuit.Emulated.Modulo

/-!
`LimbedVar::enforce_congruent` (emulated.rs:829): `self ≡ other (mod p₂)` for an unaligned `self` and
a canonical `other`. The quotient `q` is a loose hint and the circuit enforces
`self - other - q·p₂ = 0` over the integers (`enforce_equal_unaligned`).

The shape data (limbs of `q`, its sign pattern, the length of the difference) are existentially
quantified: the soundness proof holds for any of them, and a circuit that was synthesized is one
instance.
-/

namespace Sonobe
namespace Gadget

open Finset

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

def CongRel (p2 : ℕ) (selfB : ℕ → Bnd) (N : ℕ) (self e : ℕ → ZMod p1) : Prop :=
  ∃ (nq : ℕ) (neg pos : Bool) (q : ℕ → ZMod p1) (negq : ZMod p1),
    (0 < nq → neg = true ∨ pos = true) ∧ LooseRel neg pos nq q negq ∧
    ∃ nE vb len evs, N ≤ nE ∧ 8 ≤ nE ∧ nq + 7 ≤ nE ∧
      run (((p1 : ℤ) - 1) / 2) p1
          (subB (subB selfB (tightB p2)) (mulB (looseB neg pos nq) (constB p2))) nE =
        some (vb, len, evs) ∧
      EqRel (fun i => tr N self i - tr 8 e i - conv (tr nq q) (constL p1 p2) i) nE evs

/-- **`enforce_congruent` is sound**: `V - E` is a multiple of `p₂`. -/
theorem cong_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {selfB : ℕ → Bnd} {N : ℕ} {self e : ℕ → ZMod p1}
    {zS : ℕ → ℤ} (hzb : ∀ i, N ≤ i → selfB i = Bnd.zero) (hS : Valid selfB (tr N self) zS)
    (he : Canon p2 e) (h : CongRel p2 selfB N self e) :
    ∃ Q : ℤ, intVal zS N = Q * p2 + (limbsVal 8 e : ℤ) := by
  have hp1 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  have hp2' : (1 : ℤ) < p2 := by have := (Fact.out : p2.Prime).two_le; omega
  obtain ⟨nq, neg, pos, q, negq, hne, hq, nE, vb, len, evs, hN, h8, hnq, hrun, hc⟩ := h
  obtain ⟨zq, hzq⟩ := loose_valid hp1 hne hq
  have hm := const_valid (p1 := p1) p2
  have hE := tight_valid hbits he
  have hd := valid_sub (valid_sub hS hE) (valid_mul hzq hm)
  have hsum := eq_unaligned_sound (p := p1) (by simpa using lt_of_lt_of_le (by norm_num) hp.le)
    (by have : ((p1 : ℤ) - 1) / 2 < p1 := by omega
        exact this) (fun i => (hd i).1) (fun i => (hd i).2) hrun hc
  have hzq0 : ∀ i, nq ≤ i → zq i = 0 :=
    valid_zero_beyond (fun i hi => by simp [looseB, show ¬ i < nq by omega]) hzq
  have hmz0 : ∀ j, 8 ≤ j → constZ p2 j = 0 := fun j hj => by simp [constZ, show ¬ j < 8 by omega]
  have hez0 : ∀ i, 8 ≤ i → limbZ 8 e i = 0 := fun i hi => by simp [limbZ, show ¬ i < 8 by omega]
  have hSz0 : ∀ i, N ≤ i → zS i = 0 := valid_zero_beyond hzb hS
  rw [intVal_sub, intVal_sub, intVal_conv hzq0 hmz0 (by omega : nq + 8 ≤ nE + 1),
    intVal_const hp2, intVal_eq_of_zero _ h8 hez0, intVal_eq_of_zero _ hN hSz0] at hsum
  have hR : intVal (limbZ 8 e) 8 = (limbsVal 8 (tr 8 e) : ℤ) := by
    unfold intVal limbsVal
    push_cast
    refine sum_congr rfl fun i hi => ?_
    simp [limbZ, tr, mem_range.mp hi]
  have hR' : limbsVal 8 (tr 8 e) = limbsVal 8 e := by
    unfold limbsVal
    exact sum_congr rfl fun i hi => by simp [tr, mem_range.mp hi]
  refine ⟨intVal zq nq, ?_⟩
  rw [hR, hR'] at hsum
  linarith

end Gadget
end Sonobe
