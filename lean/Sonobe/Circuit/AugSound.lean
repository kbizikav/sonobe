import Sonobe.Circuit.Augmented
import Sonobe.Circuit.CFBridge
import Sonobe.IVC2.Soundness

/-!
Soundness of the augmented circuit, piece by piece: from `AugRel` to the data of
`Setup2.AugSound`.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC2 Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModAS {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]
variable (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (EA : EmuArith p1 p2) (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G : ZMod p1 × ZMod p1) (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)

/-! ### Values of the wires -/

/-- The emulated element held by coordinate slot `k`. -/
def vE (v : AugVars p1 sN) (k : Fin 12) : ZMod p2 := emuV p2 (v.pa k)

def Uraw (v : AugVars p1 sN) : RawRU (ZMod p1) (ZMod p2 × ZMod p2) :=
  ⟨(vE v 0, vE v 1), v.Uu, (vE v 2, vE v 3), fun _ => v.Ux⟩

def uinRaw (v : AugVars p1 sN) : RawIU (ZMod p1) (ZMod p2 × ZMod p2) :=
  ⟨(vE v 6, vE v 7), fun _ => v.uxIn⟩

def piRaw (v : AugVars p1 sN) : ZMod p2 × ZMod p2 := (vE v 4, vE v 5)

/-! ### 1. Base case and canonicity -/

section Basic

variable {v : AugVars p1 sN} {uux : ZMod p1}

omit [Fact p2.Prime] in
theorem aug_basecase (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    v.bc = (if v.i = 0 then 1 else 0) ∧ (v.i = 0 → v.z0 = v.zi) := by
  obtain ⟨hz, hc, -⟩ := h
  have hb := isZero_sound hz
  refine ⟨hb, fun hi => funext fun k => ?_⟩
  have hb1 : v.bc = 1 := by rw [hb, if_pos hi]
  exact condEq_sound hb1 (hc k)

theorem front_canon (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : FrontRel (p2 := p2) W2 sp dS dT pm1 v) :
    (∀ k, Canon p2 (v.pa k)) ∧ (∀ k, Canon p2 (v.sa k)) := by
  obtain ⟨h2, h3, -⟩ := h
  exact ⟨fun k => tight_canon hp hp2 (h2 k), fun k => tight_canon hp hp2 (h3 k)⟩

theorem aug_canon (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    (∀ k, Canon p2 (v.pa k)) ∧ (∀ k, Canon p2 (v.sa k)) :=
  front_canon W2 sp dS dT pm1 hp hp2 h.front

/-- An absorbed emulated variable is `encE` of its value. -/
theorem pr_ao_eq_encE {a : ℕ → ZMod p1} {w : AbsWit p1} {o : ZMod p1 × ZMod p1}
    (h32 : 2 ^ 32 ≤ p1) (hc : Canon p2 a) (h : EmuAbsRel a w o) : pr o = encE p1 p2 (emuV p2 a) := by
  obtain ⟨h1, h2⟩ := emuAbs_sound h32 h
  simp only [pr, encE, emuV_val hc, h1, h2]

/-- **The hash `u_x` of the circuit is the model hash.** -/
theorem front_ux (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : FrontRel (p2 := p2) W2 sp dS dT pm1 v) :
    v.uxIn = hsC (p2 := p2) W2 sp dS v.pp v.i v.z0 v.zi (Uraw (p2 := p2) v)
      (SecVar.val (p2 := p2) W2 (secOf v.sa v.sE v.sW)) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨cp, cs⟩ := front_canon W2 sp dS dT pm1 hp hp2 h
  obtain ⟨-, -, hsE, hsW, hU, hS, hN0, hN1, hux, -⟩ := h
  have e1 : ∀ k : Fin 4, pr (v.aoU k) = encE p1 p2 (vE v (Fin.castLE (by norm_num) k)) :=
    fun k => pr_ao_eq_encE h32 (cp _) (hU k)
  have e2 : ∀ k, pr (v.aoS k) = encE p1 p2 (emuV p2 (v.sa k)) :=
    fun k => pr_ao_eq_encE h32 (cs k) (hS k)
  have e3 := coordsOf_pt_affine W2 hsE.1 hN0
  have e4 := coordsOf_pt_affine W2 hsW.1 hN1
  rw [hux]
  unfold hsC
  congr 1
  simp only [Uraw, SecVar.val, secOf, encRU1, encRU2, encPtE, prs, List.ofFn_succ, List.ofFn_zero,
    List.flatMap_cons, List.flatMap_nil, e2, e3, e4, Fin.isValue]
  simp only [e1, vE, List.append_assoc, List.append_nil, List.cons_append, List.nil_append]
  rfl


theorem aug_ux (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    v.uxIn = hsC (p2 := p2) W2 sp dS v.pp v.i v.z0 v.zi (Uraw (p2 := p2) v)
      (SecVar.val (p2 := p2) W2 (secOf v.sa v.sE v.sW)) :=
  front_ux W2 sp dS dT pm1 hp hp2 h.front

/-- **The primary challenge**: the circuit's `ρ` is the model's Fiat–Shamir challenge. -/
theorem front_rho (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hpm : natVal 254 pm1 = p1 - 1)
    (h : FrontRel (p2 := p2) W2 sp dS dT pm1 v) :
    (∀ j < 128, IsBool (cbN v.cb j)) ∧
      natVal 128 (fun j => decide (cbN v.cb j = 1)) =
        ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) ∧
      rhoOf v.cb = ((ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) : ℕ) : ZMod p1) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨cp, cs⟩ := front_canon W2 sp dS dT pm1 hp hp2 h
  obtain ⟨-, -, -, -, -, -, -, -, -, hT, hc, hbits⟩ := h
  have e : ∀ k : Fin 8, pr (v.aoT k) = encE p1 p2 (vE v (![0, 1, 2, 3, 6, 7, 4, 5] k)) :=
    fun k => pr_ao_eq_encE h32 (cp _) (hT k)
  have e0 : pr (v.aoT 0) = encE p1 p2 (vE v 0) := e 0
  have e1 : pr (v.aoT 1) = encE p1 p2 (vE v 1) := e 1
  have e2 : pr (v.aoT 2) = encE p1 p2 (vE v 2) := e 2
  have e3 : pr (v.aoT 3) = encE p1 p2 (vE v 3) := e 3
  have e4 : pr (v.aoT 4) = encE p1 p2 (vE v 6) := e 4
  have e5 : pr (v.aoT 5) = encE p1 p2 (vE v 7) := e 5
  have e6 : pr (v.aoT 6) = encE p1 p2 (vE v 4) := e 6
  have e7 : pr (v.aoT 7) = encE p1 p2 (vE v 5) := e 7
  have hlist : ([v.Uu, v.Ux] ++ pr (v.aoT 0) ++ pr (v.aoT 1) ++ pr (v.aoT 2) ++ pr (v.aoT 3) ++
      [v.uxIn] ++ pr (v.aoT 4) ++ pr (v.aoT 5) ++ pr (v.aoT 6) ++ pr (v.aoT 7)) =
      encRU1 p1 p2 (Uraw v) ++ encIU1 p1 p2 (uinRaw v) ++ encPtE p1 p2 (piRaw v) := by
    rw [e0, e1, e2, e3, e4, e5, e6, e7]
    simp only [Uraw, uinRaw, piRaw, encRU1, encIU1, encPtE, List.append_assoc, List.cons_append,
      List.nil_append]
  have hL : v.c = hashOut sp (spInit sp v.pp dT)
      (encRU1 p1 p2 (Uraw v) ++ encIU1 p1 p2 (uinRaw v) ++ encPtE p1 p2 (piRaw v)) := by
    rw [hc, hlist]
  -- the canonical bits of `c`
  have hbv := toBits_sound (n := 254) hpm hbits
  have hrho : natVal 128 (bitsOf v.cb) = v.c.val % 2 ^ 128 := by
    rw [hbv]; exact (natVal_mod _ (by norm_num)).symm
  have hbool : ∀ j < 128, IsBool (cbN v.cb j) := by
    intro j hj
    have := hbits.1.1 ⟨j, by omega⟩
    simpa [cbN, show j < 254 by omega] using this
  have hnv : natVal 128 (fun j => decide (cbN v.cb j = 1)) = natVal 128 (bitsOf v.cb) := by
    unfold natVal
    refine sum_congr rfl fun j hj => ?_
    have := mem_range.mp hj
    simp [bitsOf, cbN, show j < 254 by omega]
  have hch : ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) = v.c.val % 2 ^ 128 := by
    unfold ch1nC; rw [hL]
  refine ⟨hbool, ?_, ?_⟩
  · rw [hnv, hrho, hch]
  · have : rhoOf v.cb = ((natVal 128 (fun j => decide (cbN v.cb j = 1)) : ℕ) : ZMod p1) :=
      sum_bits_cast (cbN v.cb) 128 hbool
    rw [this, hnv, hrho, hch]


theorem aug_rho (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hpm : natVal 254 pm1 = p1 - 1)
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    (∀ j < 128, IsBool (cbN v.cb j)) ∧
      natVal 128 (fun j => decide (cbN v.cb j = 1)) =
        ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) ∧
      rhoOf v.cb = ((ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) : ℕ) : ZMod p1) :=
  front_rho W2 sp dS dT pm1 hp hp2 hpm h.front

end Basic

/-! ### 2. The two secondary folds -/

section Secondary

variable {v : AugVars p1 sN} {uux : ZMod p1}

/-- The challenge limbs `from_bits_le` are canonical, with the value of the bits. -/
theorem rho_canon (h32 : 2 ^ 32 < p1) (hp2 : 2 ^ 128 ≤ p2) {bits : ℕ → ZMod p1}
    (hb : ∀ j < 128, IsBool (bits j)) :
    Canon p2 (rhoLimbs bits) ∧ emuV p2 (rhoLimbs bits) =
      ((natVal 128 (fun j => decide (bits j = 1)) : ℕ) : ZMod p2) := by
  obtain ⟨h1, h2, h3⟩ := rhoLimbs_val h32 bits hb
  refine ⟨⟨fun k hk => ?_, ?_⟩, by unfold emuV; rw [h3]⟩
  · by_cases hk4 : k < 4
    · exact h1 k hk4
    · rw [h2 k (by omega)]; simp
  · rw [h3]; exact lt_of_lt_of_le (natVal_lt _ _) hp2

variable [Module (ZMod p2) W2.toAffine.Point]

/-- **The two secondary folds compute `foldInstance` twice.** -/
theorem aug_fs2 (hsmul : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hG : W2.toAffine.Equation G.1 G.2) (hpm : natVal 254 pm1 = p1 - 1)
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    Canon p2 (v.o2a 0) ∧ (∀ j : Fin 7, Canon p2 (v.o2a j.succ)) ∧
      ValidPP W2 v.o2E ∧ ValidPP W2 v.o2W ∧
      (secOf v.o2a v.o2E v.o2W).val W2 =
        foldInstance ((natVal 128 (fun j => decide (v.rb1 j = 1)) : ℕ) : ZMod p2)
          (v.cp1.pt W2)
          (foldInstance ((natVal 128 (fun j => decide (v.rb0 j = 1)) : ℕ) : ZMod p2)
            (v.cp0.pt W2) ((secOf v.sa v.sE v.sW).val W2) ((cfI0 v).val W2))
          ((cfI1 v).val W2) := by
  have h32 : 2 ^ 32 < p1 := lt_of_lt_of_le (by omega : 2 ^ 32 < 2 ^ 32 + 2 ^ 33) hp.le
  obtain ⟨hbool, -⟩ := aug_rho W2 EA sp dS dT pm1 G StepRel hp hp2 hpm h
  obtain ⟨cp, cs⟩ := aug_canon W2 EA sp dS dT pm1 G StepRel hp hp2 h
  obtain ⟨-, -, -, -, hsE, hsW, -, -, -, -, -, -, -, -, hc0, hc1, hcp0, hcp1, hF1, hF2, -⟩ := h
  obtain ⟨hrc, hrv⟩ := rho_canon h32 hp2' hbool
  have hI0 : ∀ j, Canon p2 ((cfI0 v).x j) := by
    intro j; fin_cases j <;> simp [cfI0, hrc, cp]
  have hI1 : ∀ j, Canon p2 ((cfI1 v).x j) := by
    intro j; fin_cases j <;> simp [cfI1, hrc, cp]
  obtain ⟨o1u, o1x, vE1, vW1, hv1⟩ := fs2_sound W2 hsmul EA h2 hnr hord hrn h32 hG
    (U := secOf v.sa v.sE v.sW) (I := cfI0 v) (π := v.cp0) (bits := v.rb0)
    (O := secOf v.o1a v.o1E v.o1W) (cs 0) (fun j => cs j.succ) hI0 hsE hsW hc0 hcp0 hF1
  obtain ⟨o2u, o2x, vE2, vW2, hv2⟩ := fs2_sound W2 hsmul EA h2 hnr hord hrn h32 hG
    (U := secOf v.o1a v.o1E v.o1W) (I := cfI1 v) (π := v.cp1) (bits := v.rb1)
    (O := secOf v.o2a v.o2E v.o2W) o1u o1x hI1 vE1 vW1 hc1 hcp1 hF2
  refine ⟨o2u, o2x, vE2, vW2, ?_⟩
  rw [hv2, hv1]

end Secondary

end Gadget
end Sonobe

namespace Sonobe
namespace Gadget

open Finset Sonobe.IVC
open scoped Classical

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

theorem selF0_zero (v : ZMod p1) : selF0 0 v = v := by simp [selF0]
theorem selF0_one (v : ZMod p1) : selF0 1 v = 0 := by simp [selF0]

theorem selLimbs_zero (a : ℕ → ZMod p1) : selLimbs 0 a = a := by
  funext j; simp [selLimbs, selF0]

theorem selLimbs_one (a : ℕ → ZMod p1) : selLimbs 1 a = fun _ => 0 := by
  funext j; simp [selLimbs, selF0]

theorem canon_zero (hp2 : 0 < p2) : Canon p2 (fun _ : ℕ => (0 : ZMod p1)) := by
  refine ⟨fun i _ => by simp, ?_⟩
  simpa [limbsVal] using hp2

theorem emuV_zero : emuV p2 (fun _ : ℕ => (0 : ZMod p1)) = 0 := by
  simp [emuV, limbsVal]

theorem encE_zero : encE p1 p2 (0 : ZMod p2) = [0, 0] := by simp [encE]

end Gadget
end Sonobe

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC2 Sonobe.Nova Sonobe.IVC
open scoped Classical

noncomputable local instance decEqZModAS2 {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]
variable (W1 : WeierstrassCurve (ZMod p2)) [Short W1] [W1.IsElliptic]
  (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (EA : EmuArith p1 p2) (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G : ZMod p1 × ZMod p1)
  (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)
  [Module (ZMod p1) W1.toAffine.Point] [Module (ZMod p2) W2.toAffine.Point]

/-- The output hash when the base case is not active. -/
theorem aug_uux_pos {v : AugVars p1 sN} {uux : ZMod p1}
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hG : W2.toAffine.Equation G.1 G.2) (hpm : natVal 254 pm1 = p1 - 1) (hi : v.i ≠ 0)
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    uux = hsC (p2 := p2) W2 sp dS v.pp (v.i + 1) v.z0 v.nx
      ⟨(vE v 8, vE v 9), v.Uu + rhoOf v.cb, (vE v 10, vE v 11), fun _ => v.Ux + rhoOf v.cb * v.uxIn⟩
      ((secOf v.o2a v.o2E v.o2W).val W2) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨hbc, -⟩ := aug_basecase W2 EA sp dS dT pm1 G StepRel h
  have hbc0 : v.bc = 0 := by rw [hbc, if_neg hi]
  obtain ⟨cp, cs⟩ := aug_canon W2 EA sp dS dT pm1 G StepRel hp hp2 h
  obtain ⟨co2u, co2x, vE2, vW2, -⟩ := aug_fs2 W2 EA sp dS dT pm1 G StepRel hsmul2 h2 hnr hord hrn
    hp hp2 hp2' hG hpm h
  have co2 : ∀ k : Fin 8, Canon p2 (v.o2a k) := fun k => Fin.cases co2u (fun j => co2x j) k
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstp, hN, hM, hA0, hA1,
    huux⟩ := h
  rw [hbc0] at hN hM hA0 hA1 huux
  simp only [selLimbs_zero, selPP_zero, selF0_zero] at hN hM hA0 hA1 huux
  have e1 : ∀ k : Fin 4, pr (v.aoN k) = encE p1 p2 (vE v (Fin.natAdd 8 k)) :=
    fun k => pr_ao_eq_encE h32 (cp _) (hN k)
  have e2 : ∀ k : Fin 8, pr (v.aoM k) = encE p1 p2 (emuV p2 (v.o2a k)) :=
    fun k => pr_ao_eq_encE h32 (co2 k) (hM k)
  have e3 := coordsOf_pt_affine W2 vE2.1 hA0
  have e4 := coordsOf_pt_affine W2 vW2.1 hA1
  have hlist : ([v.i + 1] ++ List.ofFn v.z0 ++ List.ofFn v.nx ++ [v.Uu + rhoOf v.cb, v.uxIn * rhoOf v.cb + v.Ux] ++
      prs v.aoN ++ prs v.aoM ++ pr ((v.noM 0).x, (v.noM 0).y) ++ pr ((v.noM 1).x, (v.noM 1).y)) =
      [v.i + 1] ++ List.ofFn v.z0 ++ List.ofFn v.nx ++
        encRU1 p1 p2 ⟨(vE v 8, vE v 9), v.Uu + rhoOf v.cb, (vE v 10, vE v 11),
          fun _ => v.Ux + rhoOf v.cb * v.uxIn⟩ ++
        encRU2 (p2 := p2) W2 (SecVar.val (p2 := p2) W2 (secOf v.o2a v.o2E v.o2W)) := by
    simp only [encRU1, encRU2, encPtE, prs, SecVar.val, secOf, List.ofFn_succ, List.ofFn_zero,
      List.flatMap_cons, List.flatMap_nil, e1, e2, e3, e4, Fin.isValue]
    rw [mul_comm v.uxIn, add_comm (rhoOf v.cb * v.uxIn)]
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
    rfl
  rw [huux]
  unfold hsC
  rw [hlist]

/-- The output hash in the base case: everything selected is the zero dummy. -/
theorem aug_uux_zero {v : AugVars p1 sN} {uux : ZMod p1}
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2pos : 0 < p2) (hi : v.i = 0)
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    uux = hsC (p2 := p2) W2 sp dS v.pp (v.i + 1) v.z0 v.nx
      ⟨(0, 0), 0, (0, 0), fun _ => 0⟩ (dummyRU (ZMod p2) W2.toAffine.Point 7) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨hbc, -⟩ := aug_basecase W2 EA sp dS dT pm1 G StepRel h
  have hbc1 : v.bc = 1 := by rw [hbc, if_pos hi]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstp, hN, hM, hA0, hA1,
    huux⟩ := h
  rw [hbc1] at hN hM hA0 hA1 huux
  simp only [selLimbs_one, selPP_one, selF0_one] at hN hM hA0 hA1 huux
  have e1 : ∀ k : Fin 4, pr (v.aoN k) = [0, 0] := fun k => by
    rw [pr_ao_eq_encE h32 (canon_zero hp2pos) (hN k), emuV_zero, encE_zero]
  have e2 : ∀ k : Fin 8, pr (v.aoM k) = [0, 0] := fun k => by
    rw [pr_ao_eq_encE h32 (canon_zero hp2pos) (hM k), emuV_zero, encE_zero]
  have e3 : ((v.noM 0).x, (v.noM 0).y) = (0, 0) := by
    have := coordsOf_pt_affine W2 (zeroPP_onCurve _ _) hA0
    rw [zeroPP_pt] at this
    exact this.symm
  have e4 : ((v.noM 1).x, (v.noM 1).y) = (0, 0) := by
    have := coordsOf_pt_affine W2 (zeroPP_onCurve _ _) hA1
    rw [zeroPP_pt] at this
    exact this.symm
  rw [huux]
  unfold hsC
  have hlist : ([v.i + 1] ++ List.ofFn v.z0 ++ List.ofFn v.nx ++ [0, 0] ++
      prs v.aoN ++ prs v.aoM ++ pr ((v.noM 0).x, (v.noM 0).y) ++ pr ((v.noM 1).x, (v.noM 1).y)) =
      [v.i + 1] ++ List.ofFn v.z0 ++ List.ofFn v.nx ++
        encRU1 p1 p2 ⟨(0, 0), 0, (0, 0), fun _ => 0⟩ ++
        encRU2 (p2 := p2) W2 (dummyRU (ZMod p2) W2.toAffine.Point 7) := by
    simp only [encRU1, encRU2, encPtE, prs, dummyRU, e1, e2, e3, e4, encE_zero, List.ofFn_succ,
      List.ofFn_zero, List.flatMap_cons, List.flatMap_nil, Fin.isValue]
    simp [pr, coordsOf, encE]
  rw [hlist]

/-- **`AugSound`, derived from the augmented circuit.** -/
theorem augSound_of_circuit
    (T : Setup2 (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstep : ∀ z z', StepRel z z' → z' = T.step z)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (circ : Circuit (ZMod p1) 1 T.nw1 (AugVars p1 sN))
    (hsat : ∀ x w, T.k1.r1cs.Sat x w → circ.rel x (circ.decode w))
    (hrel : ∀ x ω, circ.rel x ω → AugRel W2 EA sp dS dT pm1 G StepRel ω (x 0))
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hG : W2.toAffine.Equation G.1 G.2) (hpm : natVal 254 pm1 = p1 - 1) :
    T.AugSound := by
  intro w' u' hinc
  have h : AugRel W2 EA sp dS dT pm1 G StepRel (circ.decode w'.w) (u'.x 0) :=
    hrel _ _ (hsat _ _ hinc.1)
  set v := circ.decode w'.w with hv
  refine ⟨v.pp, v.i, v.z0, v.zi, Uraw v, uinRaw v, piRaw v, (secOf v.sa v.sE v.sW).val W2,
    (cfI0 v).val W2, (cfI1 v).val W2, v.cp0.pt W2, v.cp1.pt W2,
    ((natVal 128 (fun j => decide (v.rb0 j = 1)) : ℕ) : ZMod p2),
    ((natVal 128 (fun j => decide (v.rb1 j = 1)) : ℕ) : ZMod p2),
    (vE v 8, vE v 9), (vE v 10, vE v 11), ?_, ?_, ?_, ?_, ?_⟩
  · exact (aug_basecase W2 EA sp dS dT pm1 G StepRel h).2
  · funext _
    simp only [uinRaw]
    rw [hhs]
    exact aug_ux W2 EA sp dS dT pm1 G StepRel hp hp2 h
  · -- first CycleFold instance
    have h32 : 2 ^ 32 < p1 := lt_of_lt_of_le (by omega : 2 ^ 32 < 2 ^ 32 + 2 ^ 33) hp.le
    obtain ⟨hbool, hn, -⟩ := aug_rho W2 EA sp dS dT pm1 G StepRel hp hp2 hpm h
    obtain ⟨-, hrv⟩ := rho_canon h32 hp2' hbool
    rw [hcfx, hch]
    funext j
    fin_cases j <;> simp [SecInc.val, cfI0, cfVec, Uraw, piRaw, vE, hrv, hn]
  · -- second CycleFold instance
    have h32 : 2 ^ 32 < p1 := lt_of_lt_of_le (by omega : 2 ^ 32 < 2 ^ 32 + 2 ^ 33) hp.le
    obtain ⟨hbool, hn, -⟩ := aug_rho W2 EA sp dS dT pm1 G StepRel hp hp2 hpm h
    obtain ⟨-, hrv⟩ := rho_canon h32 hp2' hbool
    rw [hcfx, hch]
    funext j
    fin_cases j <;> simp [SecInc.val, cfI1, cfVec, Uraw, uinRaw, vE, hrv, hn]
  · -- the output hash
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have h' := h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstp, -⟩ := h'
    have hnx : v.nx = T.step v.zi := hstep _ _ hstp
    rw [hhs]
    by_cases hi : v.i = 0
    · simp only [if_pos hi]
      have e := aug_uux_zero W2 EA sp dS dT pm1 G StepRel hp hp2 (Nat.pos_of_ne_zero (by
        intro h0; have := (Fact.out : p2.Prime).pos; omega)) hi h
      rw [e, hnx]
      have : T.rawOf (dummyRU (ZMod p1) W1.toAffine.Point 1) = ⟨(0, 0), 0, (0, 0), fun _ => 0⟩ := by
        simp [Setup2.rawOf, hco, dummyRU, coordsOf]
      rw [this]
    · simp only [if_neg hi]
      have e := aug_uux_pos W2 EA sp dS dT pm1 G StepRel hsmul2 h2 hnr hord hrn hp hp2 hp2' hG hpm hi h
      have hfold := (aug_fs2 W2 EA sp dS dT pm1 G StepRel hsmul2 h2 hnr hord hrn hp hp2 hp2' hG hpm h).2.2.2.2
      obtain ⟨-, -, hrho⟩ := aug_rho W2 EA sp dS dT pm1 G StepRel hp hp2 hpm h
      rw [e, hnx, ← hfold]
      simp only [Setup2.ch1, hch, hrho]
      have hx : ∀ ρ : ZMod p1, (Uraw (p2 := p2) v).x + ρ • (uinRaw (p2 := p2) v).x =
          fun _ => v.Ux + ρ * v.uxIn := by
        intro ρ; funext j; simp [Uraw, uinRaw]
      rw [hx]
      rfl

end Gadget
end Sonobe
