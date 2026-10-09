import Sonobe.Circuit.Augmented

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

theorem aug_canon (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    (∀ k, Canon p2 (v.pa k)) ∧ (∀ k, Canon p2 (v.sa k)) := by
  obtain ⟨-, -, h2, h3, -⟩ := h
  exact ⟨fun k => tight_canon hp hp2 (h2 k), fun k => tight_canon hp hp2 (h3 k)⟩

/-- An absorbed emulated variable is `encE` of its value. -/
theorem pr_ao_eq_encE {a : ℕ → ZMod p1} {w : AbsWit p1} {o : ZMod p1 × ZMod p1}
    (h32 : 2 ^ 32 ≤ p1) (hc : Canon p2 a) (h : EmuAbsRel a w o) : pr o = encE p1 p2 (emuV p2 a) := by
  obtain ⟨h1, h2⟩ := emuAbs_sound h32 h
  simp only [pr, encE, emuV_val hc, h1, h2]

/-- **The hash `u_x` of the circuit is the model hash.** -/
theorem aug_ux (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    v.uxIn = hsC (p2 := p2) W2 sp dS v.pp v.i v.z0 v.zi (Uraw (p2 := p2) v)
      (SecVar.val (p2 := p2) W2 (secOf v.sa v.sE v.sW)) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨cp, cs⟩ := aug_canon W2 EA sp dS dT pm1 G StepRel hp hp2 h
  obtain ⟨-, -, -, -, hsE, hsW, hU, hS, hN0, hN1, hux, -⟩ := h
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

/-- **The primary challenge**: the circuit's `ρ` is the model's Fiat–Shamir challenge. -/
theorem aug_rho (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hpm : natVal 254 pm1 = p1 - 1)
    (h : AugRel W2 EA sp dS dT pm1 G StepRel v uux) :
    (∀ j < 128, IsBool (cbN v.cb j)) ∧
      natVal 128 (fun j => decide (cbN v.cb j = 1)) =
        ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) ∧
      rhoOf v.cb = ((ch1nC (p2 := p2) sp dT v.pp (Uraw v) (uinRaw v) (piRaw v) : ℕ) : ZMod p1) := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨cp, cs⟩ := aug_canon W2 EA sp dS dT pm1 G StepRel hp hp2 h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hT, hc, hbits, -⟩ := h
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
