import Sonobe.Circuit.AugSound
import Sonobe.Circuit.FS2Complete
import Sonobe.Circuit.Emulated.Complete
import Sonobe.Circuit.CFComplete

/-!
Completeness of the augmented circuit: for honest inputs the circuit model `AugRel` has a
satisfying assignment whose public output is `Setup.augOut`.

The assignment is built gadget by gadget. Hash outputs are *defined* by the constraint that pins
them (`uxIn`, `c`, the squeezed secondary challenges, `uux`) and then identified with the model
hashes by the soundness lemmas of `AugSound`.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModAC {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

section Basics

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- The top limb of a canonical value is below `2^30`. -/
theorem top_lt (hp2 : p2 ≤ 2 ^ 254) {a : ℕ → ZMod p1} (h : Canon p2 a) : (a 7).val < 2 ^ 30 := by
  have h1 : (a 7).val * 2 ^ (32 * 7) ≤ limbsVal 8 a := by
    unfold limbsVal
    rw [show (8 : ℕ) = 7 + 1 by norm_num, sum_range_succ]
    omega
  have h2 := h.2
  by_contra hcon
  have : 2 ^ 30 * 2 ^ (32 * 7) ≤ (a 7).val * 2 ^ (32 * 7) :=
    Nat.mul_le_mul_right _ (not_lt.mp hcon)
  have h3 : (2 : ℕ) ^ 254 ≤ 2 ^ 30 * 2 ^ (32 * 7) := by norm_num
  omega

/-- **Every canonical emulated variable has an `absorb_into` witness**, whose output is the native
encoding of its value. -/
theorem absPair_exists (h32 : 2 ^ 32 ≤ p1) (hp2 : p2 ≤ 2 ^ 254) {a : ℕ → ZMod p1}
    (h : Canon p2 a) : ∃ (w : AbsWit p1) (o : ZMod p1 × ZMod p1), EmuAbsRel a w o ∧
      pr o = encE p1 p2 (emuV p2 a) := by
  have hl : ∀ i < 7, (a i).val < 2 ^ 32 := fun i hi => h.1 i (by omega)
  obtain ⟨w, hw⟩ := emuAbs_complete h32 hl (top_lt hp2 h)
  refine ⟨w, _, hw, ?_⟩
  simp [pr, encE, emuV_val h]

/-- A group element as the output of a fresh `to_affine`. -/
theorem affPair_exists (W : WeierstrassCurve (ZMod p1)) [Short W] [W.IsElliptic] {P : PP (ZMod p1)}
    (hP : P.OnCurve W.a₄ W.a₆) : ∃ w : AffWit (ZMod p1), AffRel P w ∧
      (w.x, w.y) = coordsOf W (P.pt W) := by
  obtain ⟨inf, zinv, inv, h⟩ := toAffine_complete_coords W hP
  exact ⟨⟨_, _, inf, zinv, inv⟩, h, rfl⟩

theorem absFam_exists (h32 : 2 ^ 32 ≤ p1) (hp2 : p2 ≤ 2 ^ 254) {n : ℕ}
    {a : Fin n → ℕ → ZMod p1} (h : ∀ k, Canon p2 (a k)) :
    ∃ (aw : Fin n → AbsWit p1) (ao : Fin n → ZMod p1 × ZMod p1), ∀ k, EmuAbsRel (a k) (aw k) (ao k) := by
  have := fun k => absPair_exists (p2 := p2) h32 hp2 (h k)
  choose aw ao hrel _ using this
  exact ⟨aw, ao, hrel⟩

theorem secOf_cons {F : Type*} (O : SecVar F) :
    secOf (Fin.cons O.u O.x : Fin 8 → ℕ → F) O.cmE O.cmW = O := by
  cases O; rfl

end Basics

section Helpers

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]

theorem bool_of_toBits {pm1 : ℕ → Bool} {c : ZMod p1} {cb : Fin 254 → ZMod p1}
    (hbits : ToBitsRel 254 pm1 c cb) : ∀ j < 128, IsBool (cbN cb j) := by
  intro j hj
  have := hbits.1.1 ⟨j, by omega⟩
  simpa [cbN, show j < 254 by omega] using this

theorem cbN_val {pm1 : ℕ → Bool} (hpm : natVal 254 pm1 = p1 - 1) {c : ZMod p1}
    {cb : Fin 254 → ZMod p1} (hbits : ToBitsRel 254 pm1 c cb) :
    natVal 128 (fun j => decide (cbN cb j = 1)) = c.val % 2 ^ 128 := by
  have hbv := toBits_sound (n := 254) hpm hbits
  have hrho : natVal 128 (bitsOf cb) = c.val % 2 ^ 128 := by
    rw [hbv]; exact (natVal_mod _ (by norm_num)).symm
  rw [← hrho]
  unfold natVal
  refine sum_congr rfl fun j hj => ?_
  have := mem_range.mp hj
  simp [bitsOf, cbN, show j < 254 by omega]

theorem canon_selLimbs (hp2 : 0 < p2) {bc : ZMod p1} (hbc : bc = 0 ∨ bc = 1) {a : ℕ → ZMod p1}
    (h : Canon p2 a) : Canon p2 (selLimbs bc a) := by
  rcases hbc with rfl | rfl
  · rw [selLimbs_zero]; exact h
  · rw [selLimbs_one]; exact canon_zero hp2

theorem primList_enc {v : AugVars p1 sN} (h32 : 2 ^ 32 ≤ p1) (cp : ∀ k, Canon p2 (v.pa k))
    (hT : ∀ k : Fin 8, EmuAbsRel (v.pa (![0, 1, 2, 3, 6, 7, 4, 5] k)) (v.awT k) (v.aoT k)) :
    primList v = encRU1 p1 p2 (Uraw (p2 := p2) v) ++ encIU1 p1 p2 (uinRaw (p2 := p2) v) ++
      encPtE p1 p2 (piRaw (p2 := p2) v) := by
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
  unfold primList
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  simp only [Uraw, uinRaw, piRaw, encRU1, encIU1, encPtE, List.append_assoc, List.cons_append,
    List.nil_append]

theorem prs_eq {n : ℕ} {ao : Fin n → ZMod p1 × ZMod p1} {e : Fin n → List (ZMod p1)}
    (h : ∀ k, pr (ao k) = e k) : prs ao = (List.ofFn e).flatten := by
  unfold prs
  rw [List.flatMap, List.map_ofFn]
  congr 2
  funext k; exact h k

theorem flatten_ofFn_succ {n : ℕ} (e : Fin (n + 1) → List (ZMod p1)) :
    (List.ofFn e).flatten = e 0 ++ (List.ofFn fun j : Fin n => e j.succ).flatten := by
  rw [List.ofFn_succ]; simp

/-- The list absorbed for one secondary fold (`cf_U`, `cf_u`, `cf_π`) is the model encoding. -/
theorem chalList_enc (W : WeierstrassCurve (ZMod p1)) [Short W] [W.IsElliptic]
    (h32 : 2 ^ 32 ≤ p1) (hp2b : p2 ≤ 2 ^ 254) (hp2e : p2 ≤ 2 ^ (32 * 8))
    {a : Fin 8 → ℕ → ZMod p1} (ha : ∀ k, Canon p2 (a k))
    {aw : Fin 8 → AbsWit p1} {ao : Fin 8 → ZMod p1 × ZMod p1}
    (hA : ∀ k, EmuAbsRel (a k) (aw k) (ao k)) {E Wp : PP (ZMod p1)} {nE nW : AffWit (ZMod p1)}
    (hnE : (nE.x, nE.y) = coordsOf W (E.pt W)) (hnW : (nW.x, nW.y) = coordsOf W (Wp.pt W))
    (I : SecInc (ZMod p1)) (hIc : ∀ j, Canon p2 (I.x j))
    {awI : Fin 7 → AbsWit p1} {aoI : Fin 7 → ZMod p1 × ZMod p1}
    (hAI : ∀ j, EmuAbsRel (I.x j) (awI j) (aoI j)) {n0 np : AffWit (ZMod p1)} {P : PP (ZMod p1)}
    (hn0 : (n0.x, n0.y) = coordsOf W (I.cmW.pt W)) (hnp : (np.x, np.y) = coordsOf W (P.pt W)) :
    prs ao ++ pr (nE.x, nE.y) ++ pr (nW.x, nW.y) ++ prs aoI ++ pr (n0.x, n0.y) ++ pr (np.x, np.y) =
      encRU2 (p2 := p2) W (SecVar.val (p2 := p2) W (secOf a E Wp)) ++
        encIU2 (p2 := p2) W (SecInc.val (p2 := p2) W I) ++ pr (coordsOf W (P.pt W)) := by
  have e1 : ∀ k, pr (ao k) = encE p1 p2 (emuV p2 (a k)) := fun k =>
    pr_ao_eq_encE h32 (ha k) (hA k)
  have e2 : ∀ j, pr (aoI j) = encE p1 p2 (emuV p2 (I.x j)) := fun j =>
    pr_ao_eq_encE h32 (hIc j) (hAI j)
  rw [prs_eq e1, prs_eq e2, flatten_ofFn_succ, hnE, hnW, hn0, hnp]
  simp only [encRU2, encIU2, SecVar.val, SecInc.val, secOf, List.append_assoc]

end Helpers

section Main

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]
  (W1 : WeierstrassCurve (ZMod p2)) [Short W1] [W1.IsElliptic]
  (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (EA : EmuArith p1 p2) (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G : ZMod p1 × ZMod p1)
  (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)
  [Module (ZMod p1) W1.toAffine.Point] [Module (ZMod p2) W2.toAffine.Point]

/-- **An honest assignment of the augmented circuit exists**, and its public output is
`Setup.augOut`. -/
theorem aug_witness
    (T : Setup (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hch2a : T.ch2an = ch2anC W2 sp dT) (hch2b : T.ch2bn = ch2bnC W2 sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstepc : ∀ z, StepRel z (T.step z)) (hEA : EA.Complete)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hp1b : p1 ≤ 2 ^ 254) (hp2b : p2 ≤ 2 ^ 254)
    (hG : W2.toAffine.Equation G.1 G.2) (hpm : natVal 254 pm1 = p1 - 1)
    (i : ℕ) (z0 zi : Fin sN → ZMod p1) (U : RunningInstance (ZMod p1) W1.toAffine.Point 1)
    (u : IncomingInstance W1.toAffine.Point (ZMod p1) 1) (π : W1.toAffine.Point)
    (cfU : RunningInstance (ZMod p2) W2.toAffine.Point 7)
    (cu0 cu1 : IncomingInstance W2.toAffine.Point (ZMod p2) 7) (cπ0 cπ1 : W2.toAffine.Point)
    (hcast : ((i : ℕ) : ZMod p1) = 0 → i = 0) (hi0 : i = 0 → z0 = zi)
    (hux : u.x = fun _ => T.hs T.pph (i : ZMod p1) z0 zi (T.rawOf U) cfU)
    (hx0 : cu0.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmE)
      (T.coords π) (T.coords (T.fold1 U u π).cmE))
    (hx1 : cu1.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmW)
      (T.coords u.cmW) (T.coords (T.fold1 U u π).cmW)) :
    ∃ (v : AugVars p1 sN) (uux : ZMod p1), AugRel W2 EA sp dS dT pm1 G StepRel v uux ∧
      uux = T.augOut i z0 zi U u π cfU cu0 cu1 cπ0 cπ1 := by
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  have h32' : 2 ^ 32 < p1 := lt_of_lt_of_le (by omega : 2 ^ 32 < 2 ^ 32 + 2 ^ 33) hp.le
  have hp2e : p2 ≤ 2 ^ (32 * 8) := hp2.le
  have hp2pos : 0 < p2 := (Fact.out : p2.Prime).pos
  have hb2 : W2.a₆ ≠ 0 := by
    intro h0; apply hnr 0; simpa [h0] using h0
  -- coordinates of the primary points, as values of the emulated field
  set F1 := T.fold1 U u π with hF1
  set cs : Fin 12 → ZMod p2 :=
    ![(coordsOf W1 U.cmE).1, (coordsOf W1 U.cmE).2, (coordsOf W1 U.cmW).1, (coordsOf W1 U.cmW).2,
      (coordsOf W1 π).1, (coordsOf W1 π).2, (coordsOf W1 u.cmW).1, (coordsOf W1 u.cmW).2,
      (coordsOf W1 F1.cmE).1, (coordsOf W1 F1.cmE).2, (coordsOf W1 F1.cmW).1,
      (coordsOf W1 F1.cmW).2] with hcs
  set pa : Fin 12 → ℕ → ZMod p1 := fun k => limbsOf p1 (cs k) with hpa
  have hpa_canon : ∀ k, Canon p2 (pa k) := fun k => canon_limbsOf h32 hp2e (cs k)
  have htight : ∀ k, ∃ w, TightRel 8 32 (mlimb p2) (pa k) w := fun k => tight_complete hp hp2 (cs k)
  choose pw hpw using htight
  -- the secondary running instance
  set sv : Fin 8 → ZMod p2 := Fin.cons cfU.u cfU.x with hsv
  set sa : Fin 8 → ℕ → ZMod p1 := fun k => limbsOf p1 (sv k) with hsa
  have hsa_canon : ∀ k, Canon p2 (sa k) := fun k => canon_limbsOf h32 hp2e (sv k)
  have htight2 : ∀ k, ∃ w, TightRel 8 32 (mlimb p2) (sa k) w := fun k => tight_complete hp hp2 (sv k)
  choose sw hsw using htight2
  set sE := ppOf W2 cfU.cmE with hsE
  set sW := ppOf W2 cfU.cmW with hsW
  set c0W := ppOf W2 cu0.cmW with hc0W
  set c1W := ppOf W2 cu1.cmW with hc1W
  set cp0 := ppOf W2 cπ0 with hcp0
  set cp1 := ppOf W2 cπ1 with hcp1
  have hvE : ValidPP W2 sE := ppOf_valid W2 hb2 _
  have hvW : ValidPP W2 sW := ppOf_valid W2 hb2 _
  have hv0 : ValidPP W2 c0W := ppOf_valid W2 hb2 _
  have hv1 : ValidPP W2 c1W := ppOf_valid W2 hb2 _
  have hvp0 : ValidPP W2 cp0 := ppOf_valid W2 hb2 _
  have hvp1 : ValidPP W2 cp1 := ppOf_valid W2 hb2 _
  -- base case flag
  obtain ⟨bc, invI, hzr, hbc⟩ := isZero_complete ((i : ℕ) : ZMod p1)
  have hbc01 : bc = 0 ∨ bc = 1 := by rw [hbc]; split_ifs <;> simp
  have hcond : ∀ k, CondEqRel bc (z0 k) (zi k) := by
    intro k
    unfold CondEqRel
    by_cases h : ((i : ℕ) : ZMod p1) = 0
    · have := hi0 (hcast h); rw [this]; simp
    · rw [hbc, if_neg h]; simp
  -- the hash of the state
  obtain ⟨awU, aoU, hU⟩ := absFam_exists (p2 := p2) h32 hp2b
    (a := fun k : Fin 4 => pa (Fin.castLE (by norm_num) k)) (fun k => hpa_canon _)
  obtain ⟨awS, aoS, hS⟩ := absFam_exists (p2 := p2) h32 hp2b (a := sa) hsa_canon
  obtain ⟨nE, hnE, -⟩ := affPair_exists W2 hvE.1
  obtain ⟨nW, hnW, -⟩ := affPair_exists W2 hvW.1
  set uxIn : ZMod p1 := hashOut sp (spInit sp T.pph dS)
    ([((i : ℕ) : ZMod p1)] ++ List.ofFn z0 ++ List.ofFn zi ++ [U.u, U.x 0] ++ prs aoU ++ prs aoS ++
      pr (nE.x, nE.y) ++ pr (nW.x, nW.y)) with huxIn
  -- the primary challenge
  obtain ⟨awT, aoT, hT⟩ := absFam_exists (p2 := p2) h32 hp2b
    (a := fun k : Fin 8 => pa (![0, 1, 2, 3, 6, 7, 4, 5] k)) (fun k => hpa_canon _)
  set c : ZMod p1 := hashOut sp (spInit sp T.pph dT)
    ([U.u, U.x 0] ++ pr (aoT 0) ++ pr (aoT 1) ++ pr (aoT 2) ++ pr (aoT 3) ++ [uxIn] ++
      pr (aoT 4) ++ pr (aoT 5) ++ pr (aoT 6) ++ pr (aoT 7)) with hc
  obtain ⟨cb, hcb⟩ := toBits_complete (n := 254) hpm (by simpa using hp1b) c
  have hcbool : ∀ j < 128, IsBool (cbN cb j) := bool_of_toBits hcb
  obtain ⟨hrhoCanon, hrhoV⟩ := rho_canon h32' hp2' hcbool
  -- first secondary fold
  set I0 : SecInc (ZMod p1) :=
    ⟨![rhoLimbs (cbN cb), pa 0, pa 1, pa 4, pa 5, pa 8, pa 9], c0W⟩ with hI0
  have hI0canon : ∀ j, Canon p2 (I0.x j) := by
    intro j; fin_cases j
    · exact hrhoCanon
    all_goals exact hpa_canon _
  obtain ⟨awS', aoS', hS'⟩ := absFam_exists (p2 := p2) h32 hp2b (a := sa) hsa_canon
  obtain ⟨nE', hnE', hnE'c⟩ := affPair_exists W2 hvE.1
  obtain ⟨nW', hnW', hnW'c⟩ := affPair_exists W2 hvW.1
  obtain ⟨awI0, aoI0, hAI0⟩ := absFam_exists (p2 := p2) h32 hp2b (a := I0.x) hI0canon
  obtain ⟨n0', hn0', hn0'c⟩ := affPair_exists W2 hv0.1
  obtain ⟨np0, hnp0, hnp0c⟩ := affPair_exists W2 hvp0.1
  set L1 : List (ZMod p1) := prs aoS' ++ pr (nE'.x, nE'.y) ++ pr (nW'.x, nW'.y) ++ prs aoI0 ++
    pr (n0'.x, n0'.y) ++ pr (np0.x, np0.y) with hL1
  set S1 := (chalStep sp (spInit sp T.pph dT) ([U.u, U.x 0] ++ pr (aoT 0) ++ pr (aoT 1) ++
    pr (aoT 2) ++ pr (aoT 3) ++ [uxIn] ++ pr (aoT 4) ++ pr (aoT 5) ++ pr (aoT 6) ++
    pr (aoT 7))).2 with hS1
  set c2 : ZMod p1 := (chalStep sp S1 L1).1 with hc2
  obtain ⟨cb2, hcb2⟩ := toBits_complete (n := 254) hpm (by simpa using hp1b) c2
  set rb0 : ℕ → ZMod p1 := fun j => cbN cb2 j with hrb0
  have hrb0b : ∀ j < 128, IsBool (rb0 j) := bool_of_toBits hcb2
  obtain ⟨O1, hO1⟩ := fs2_complete W2 EA hEA h2 hnr hord hrn h32' hG (U := secOf sa sE sW)
    (I := I0) (π := cp0) (bits := rb0) hrb0b (hsa_canon 0) (fun j => hsa_canon _) hI0canon hvE
    hvW hv0 hvp0.1
  obtain ⟨cO1u, cO1x, vO1E, vO1W, hO1v⟩ := fs2_sound W2 hsmul2 EA h2 hnr hord hrn h32' hG
    (hsa_canon 0) (fun j => hsa_canon _) hI0canon hvE hvW hv0 hvp0.1 hO1
  set o1a : Fin 8 → ℕ → ZMod p1 := Fin.cons O1.u O1.x with ho1a
  have ho1a_canon : ∀ k, Canon p2 (o1a k) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact cO1u
    · exact cO1x j
  have hsecO1 : secOf o1a O1.cmE O1.cmW = O1 := secOf_cons O1
  -- second secondary fold
  set I1 : SecInc (ZMod p1) :=
    ⟨![rhoLimbs (cbN cb), pa 2, pa 3, pa 6, pa 7, pa 10, pa 11], c1W⟩ with hI1
  have hI1canon : ∀ j, Canon p2 (I1.x j) := by
    intro j; fin_cases j
    · exact hrhoCanon
    all_goals exact hpa_canon _
  obtain ⟨awO1, aoO1, hAO1⟩ := absFam_exists (p2 := p2) h32 hp2b (a := o1a) ho1a_canon
  obtain ⟨nO1E, hnO1E, hnO1Ec⟩ := affPair_exists W2 vO1E.1
  obtain ⟨nO1W, hnO1W, hnO1Wc⟩ := affPair_exists W2 vO1W.1
  obtain ⟨awI1, aoI1, hAI1⟩ := absFam_exists (p2 := p2) h32 hp2b (a := I1.x) hI1canon
  obtain ⟨n1', hn1', hn1'c⟩ := affPair_exists W2 hv1.1
  obtain ⟨np1, hnp1, hnp1c⟩ := affPair_exists W2 hvp1.1
  set L2 : List (ZMod p1) := prs aoO1 ++ pr (nO1E.x, nO1E.y) ++ pr (nO1W.x, nO1W.y) ++ prs aoI1 ++
    pr (n1'.x, n1'.y) ++ pr (np1.x, np1.y) with hL2
  set c3 : ZMod p1 := (chalStep sp (chalStep sp S1 L1).2 L2).1 with hc3
  obtain ⟨cb3, hcb3⟩ := toBits_complete (n := 254) hpm (by simpa using hp1b) c3
  set rb1 : ℕ → ZMod p1 := fun j => cbN cb3 j with hrb1
  have hrb1b : ∀ j < 128, IsBool (rb1 j) := bool_of_toBits hcb3
  obtain ⟨O2, hO2⟩ := fs2_complete W2 EA hEA h2 hnr hord hrn h32' hG (U := secOf o1a O1.cmE O1.cmW)
    (I := I1) (π := cp1) (bits := rb1) hrb1b cO1u (fun j => cO1x j) hI1canon vO1E vO1W hv1 hvp1.1
  obtain ⟨cO2u, cO2x, vO2E, vO2W, hO2v⟩ := fs2_sound W2 hsmul2 EA h2 hnr hord hrn h32' hG
    cO1u (fun j => cO1x j) hI1canon vO1E vO1W hv1 hvp1.1 hO2
  set o2a : Fin 8 → ℕ → ZMod p1 := Fin.cons O2.u O2.x with ho2a
  have ho2a_canon : ∀ k, Canon p2 (o2a k) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact cO2u
    · exact cO2x j
  have hsecO2 : secOf o2a O2.cmE O2.cmW = O2 := secOf_cons O2
  -- the next state and the output hash
  set nx : Fin sN → ZMod p1 := T.step zi with hnx
  obtain ⟨awN, aoN, hN⟩ := absFam_exists (p2 := p2) h32 hp2b
    (a := fun k : Fin 4 => selLimbs bc (pa (Fin.natAdd 8 k)))
    (fun k => canon_selLimbs hp2pos hbc01 (hpa_canon _))
  obtain ⟨awM, aoM, hM⟩ := absFam_exists (p2 := p2) h32 hp2b
    (a := fun k : Fin 8 => selLimbs bc (o2a k)) (fun k => canon_selLimbs hp2pos hbc01 (ho2a_canon _))
  have hsel : ∀ P : PP (ZMod p1), P.OnCurve W2.a₄ W2.a₆ →
      (selPP bc zeroPP P).OnCurve W2.a₄ W2.a₆ := by
    intro P hP
    rcases hbc01 with h | h <;> rw [h]
    · rw [selPP_zero]; exact hP
    · rw [selPP_one]; exact zeroPP_onCurve _ _
  obtain ⟨nM0, hnM0, -⟩ := affPair_exists W2 (hsel _ vO2E.1)
  obtain ⟨nM1, hnM1, -⟩ := affPair_exists W2 (hsel _ vO2W.1)
  set uux : ZMod p1 := hashOut sp (spInit sp T.pph dS)
    ([((i : ℕ) : ZMod p1) + 1] ++ List.ofFn z0 ++ List.ofFn nx ++
      [selF0 bc (U.u + rhoOf cb), selF0 bc (uxIn * rhoOf cb + U.x 0)] ++
      prs aoN ++ prs aoM ++ pr (nM0.x, nM0.y) ++ pr (nM1.x, nM1.y)) with huux
  let v : AugVars p1 sN :=
    { pp := T.pph, i := ((i : ℕ) : ZMod p1), invI := invI, bc := bc, z0 := z0, zi := zi,
      nx := nx, Uu := U.u, Ux := U.x 0, uxIn := uxIn, pa := pa, pw := pw, sa := sa, sw := sw,
      sE := sE, sW := sW, c0W := c0W, c1W := c1W, cp0 := cp0, cp1 := cp1, rb0 := rb0, rb1 := rb1,
      o1a := o1a, o1E := O1.cmE, o1W := O1.cmW, o2a := o2a, o2E := O2.cmE, o2W := O2.cmW,
      c := c, cb := cb, awU := awU, aoU := aoU, awS := awS, aoS := aoS, noU := ![nE, nW],
      awT := awT, aoT := aoT, awN := awN, aoN := aoN, awM := awM, aoM := aoM,
      noM := ![nM0, nM1] }
  have hrel : AugRel W2 EA sp dS dT pm1 G StepRel v uux := by
    refine ⟨hzr, hcond, hpw, hsw, hvE, hvW, hU, hS, hnE, hnW, rfl, hT, rfl, hcb, hv0, hv1,
      hvp0.1, hvp1.1, ?_, ?_, hstepc zi, hN, hM, hnM0, hnM1, rfl, ?_⟩
    · rw [hsecO1] at hO2
      exact hO1
    · rw [hsecO2]; exact hO2
    · exact ⟨prs aoS', pr (nE'.x, nE'.y), pr (nW'.x, nW'.y), prs aoI0, pr (n0'.x, n0'.y),
        pr (np0.x, np0.y), prs aoO1, pr (nO1E.x, nO1E.y), pr (nO1W.x, nO1W.y), prs aoI1,
        pr (n1'.x, n1'.y), pr (np1.x, np1.y), cb2, cb3, ⟨awS', aoS', hS', rfl⟩, ⟨nE', hnE', rfl⟩,
        ⟨nW', hnW', rfl⟩, ⟨awI0, aoI0, hAI0, rfl⟩, ⟨n0', hn0', rfl⟩, ⟨np0, hnp0, rfl⟩, hcb2,
        fun j _ => rfl, ⟨awO1, aoO1, hAO1, rfl⟩, ⟨nO1E, hnO1E, rfl⟩, ⟨nO1W, hnO1W, rfl⟩,
        ⟨awI1, aoI1, hAI1, rfl⟩, ⟨n1', hn1', rfl⟩, ⟨np1, hnp1, rfl⟩, hcb3, fun j _ => rfl⟩
  refine ⟨v, uux, hrel, ?_⟩
  -- identification of the circuit values with the model
  have hco' : ∀ P, T.coords P = coordsOf W1 P := fun P => by rw [hco]
  have hvE_eq : ∀ k, vE v k = cs k := fun k => emuV_limbsOf h32 hp2e (cs k)
  have cs0 : cs 0 = (coordsOf W1 U.cmE).1 := rfl
  have cs1 : cs 1 = (coordsOf W1 U.cmE).2 := rfl
  have cs2 : cs 2 = (coordsOf W1 U.cmW).1 := rfl
  have cs3 : cs 3 = (coordsOf W1 U.cmW).2 := rfl
  have cs4 : cs 4 = (coordsOf W1 π).1 := rfl
  have cs5 : cs 5 = (coordsOf W1 π).2 := rfl
  have cs6 : cs 6 = (coordsOf W1 u.cmW).1 := rfl
  have cs7 : cs 7 = (coordsOf W1 u.cmW).2 := rfl
  have cs8 : cs 8 = (coordsOf W1 F1.cmE).1 := rfl
  have cs9 : cs 9 = (coordsOf W1 F1.cmE).2 := rfl
  have cs10 : cs 10 = (coordsOf W1 F1.cmW).1 := rfl
  have cs11 : cs 11 = (coordsOf W1 F1.cmW).2 := rfl
  have hUraw : Uraw (p2 := p2) v = T.rawOf U := by
    have hx : (fun _ : Fin 1 => U.x 0) = U.x := by funext j; rw [Subsingleton.elim j 0]
    simp only [Uraw, Setup.rawOf, hco', hvE_eq, cs0, cs1, cs2, cs3, Prod.mk.eta]
    exact congrArg (RawRU.mk _ _ _) hx
  have hpiRaw : piRaw (p2 := p2) v = T.coords π := by
    simp only [piRaw, hco', hvE_eq, cs4, cs5, Prod.mk.eta]
  have hcanonV : ∀ k, Canon p2 (v.pa k) := hpa_canon
  -- `u_x`
  have hFront := hrel.front
  have hSecV : (secOf v.sa v.sE v.sW).val W2 = cfU := by
    have h0 : ∀ k, emuV p2 (sa k) = sv k := fun k => emuV_limbsOf h32 hp2e (sv k)
    show SecVar.val W2 (secOf sa sE sW) = cfU
    cases cfU
    simp only [SecVar.val, secOf, h0, hsE, hsW, ppOf_pt, hsv, Fin.cons_zero, Fin.cons_succ]
  have hux' : v.uxIn = u.x 0 := by
    rw [front_ux W2 sp dS dT pm1 hp hp2 hFront, hux]
    show _ = T.hs T.pph (i : ZMod p1) z0 zi (T.rawOf U) cfU
    rw [hhs, hSecV, hUraw]
  have hUin : uinRaw (p2 := p2) v = T.rawOfI u := by
    have hx : (fun _ : Fin 1 => u.x 0) = u.x := by funext j; rw [Subsingleton.elim j 0]
    simp only [uinRaw, Setup.rawOfI, hco', hvE_eq, cs6, cs7, Prod.mk.eta, hux']
    exact congrArg (RawIU.mk _) hx
  obtain ⟨hbool', hnatv, hrhoV'⟩ := aug_rho W2 EA sp dS dT pm1 G StepRel hp hp2 hpm hrel
  have hch1 : T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) =
      ch1nC (p2 := p2) sp dT v.pp (Uraw (p2 := p2) v) (uinRaw (p2 := p2) v) (piRaw (p2 := p2) v) := by
    rw [hch, hUraw, hUin, hpiRaw]
  have hnat1 : natVal 128 (fun j => decide (cbN cb j = 1)) =
      T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) := by rw [hch1]; exact hnatv
  have hrho1 : rhoOf cb = ((T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) : ℕ) : ZMod p1) := by
    rw [hch1]; exact hrhoV'
  -- the CycleFold instances
  have ePa : ∀ k, emuV p2 (pa k) = cs k := fun k => emuV_limbsOf h32 hp2e (cs k)
  have hI0x : ∀ j, emuV p2 (I0.x j) = cu0.x j := by
    intro j
    rw [hx0, hcfx]
    have h0 : emuV p2 (I0.x 0) = ((T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) : ℕ) : ZMod p2) := by
      show emuV p2 (rhoLimbs (cbN cb)) = _
      rw [hrhoV, hnat1]
    have h1 : emuV p2 (I0.x 1) = (coordsOf W1 U.cmE).1 := by
      show emuV p2 (pa 0) = _; rw [ePa, cs0]
    have h2' : emuV p2 (I0.x 2) = (coordsOf W1 U.cmE).2 := by
      show emuV p2 (pa 1) = _; rw [ePa, cs1]
    have h3 : emuV p2 (I0.x 3) = (coordsOf W1 π).1 := by
      show emuV p2 (pa 4) = _; rw [ePa, cs4]
    have h4 : emuV p2 (I0.x 4) = (coordsOf W1 π).2 := by
      show emuV p2 (pa 5) = _; rw [ePa, cs5]
    have h5 : emuV p2 (I0.x 5) = (coordsOf W1 F1.cmE).1 := by
      show emuV p2 (pa 8) = _; rw [ePa, cs8]
    have h6 : emuV p2 (I0.x 6) = (coordsOf W1 F1.cmE).2 := by
      show emuV p2 (pa 9) = _; rw [ePa, cs9]
    fin_cases j
    · simpa [cfVec] using h0
    · simpa [cfVec, hco'] using h1
    · simpa [cfVec, hco'] using h2'
    · simpa [cfVec, hco'] using h3
    · simpa [cfVec, hco'] using h4
    · simpa [cfVec, hco'] using h5
    · simpa [cfVec, hco'] using h6
  have hI1x : ∀ j, emuV p2 (I1.x j) = cu1.x j := by
    intro j
    rw [hx1, hcfx]
    have h0 : emuV p2 (I1.x 0) = ((T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) : ℕ) : ZMod p2) := by
      show emuV p2 (rhoLimbs (cbN cb)) = _
      rw [hrhoV, hnat1]
    have h1 : emuV p2 (I1.x 1) = (coordsOf W1 U.cmW).1 := by
      show emuV p2 (pa 2) = _; rw [ePa, cs2]
    have h2' : emuV p2 (I1.x 2) = (coordsOf W1 U.cmW).2 := by
      show emuV p2 (pa 3) = _; rw [ePa, cs3]
    have h3 : emuV p2 (I1.x 3) = (coordsOf W1 u.cmW).1 := by
      show emuV p2 (pa 6) = _; rw [ePa, cs6]
    have h4 : emuV p2 (I1.x 4) = (coordsOf W1 u.cmW).2 := by
      show emuV p2 (pa 7) = _; rw [ePa, cs7]
    have h5 : emuV p2 (I1.x 5) = (coordsOf W1 F1.cmW).1 := by
      show emuV p2 (pa 10) = _; rw [ePa, cs10]
    have h6 : emuV p2 (I1.x 6) = (coordsOf W1 F1.cmW).2 := by
      show emuV p2 (pa 11) = _; rw [ePa, cs11]
    fin_cases j
    · simpa [cfVec] using h0
    · simpa [cfVec, hco'] using h1
    · simpa [cfVec, hco'] using h2'
    · simpa [cfVec, hco'] using h3
    · simpa [cfVec, hco'] using h4
    · simpa [cfVec, hco'] using h5
    · simpa [cfVec, hco'] using h6
  have hI0val : SecInc.val (p2 := p2) W2 I0 = cu0 := by
    cases cu0
    simp only [SecInc.val, I0, hc0W, ppOf_pt]
    exact congrArg (IncomingInstance.mk _) (funext fun j => hI0x j)
  have hI1val : SecInc.val (p2 := p2) W2 I1 = cu1 := by
    cases cu1
    simp only [SecInc.val, I1, hc1W, ppOf_pt]
    exact congrArg (IncomingInstance.mk _) (funext fun j => hI1x j)
  -- the secondary challenges
  have hcp0pt : cp0.pt W2 = cπ0 := ppOf_pt W2 cπ0
  have hcp1pt : cp1.pt W2 = cπ1 := ppOf_pt W2 cπ1
  have hSecV0 : SecVar.val (p2 := p2) W2 (secOf sa sE sW) = cfU := hSecV
  have hS1' : S1 = primState sp dT T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) := by
    rw [hS1]; unfold primState
    have hl := primList_enc (p2 := p2) (v := v) h32 hpa_canon hT
    rw [hUraw, hUin, hpiRaw] at hl
    exact congrArg (fun L => (chalStep sp (spInit sp T.pph dT) L).2) hl
  have hL1' : L1 = encRU2 W2 cfU ++ encIU2 W2 cu0 ++ pr (coordsOf W2 cπ0) := by
    have := chalList_enc W2 h32 hp2b hp2e hsa_canon hS' hnE'c hnW'c I0 hI0canon hAI0 hn0'c hnp0c
    rw [hSecV0, hI0val, hcp0pt] at this
    exact this
  have hc2' : c2 = (sec1C W2 sp dT T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0).1 := by
    unfold sec1C; rw [← hS1', ← hL1']
  have hnat2 : natVal 128 (fun j => decide (rb0 j = 1)) =
      T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 := by
    show natVal 128 (fun j => decide (cbN cb2 j = 1)) = _
    rw [cbN_val hpm hcb2, hch2a]
    unfold ch2anC
    rw [hc2']
  have hO1val : SecVar.val (p2 := p2) W2 O1 = T.cfFold1 U u π cfU cu0 cπ0 := by
    rw [hO1v, hnat2, hcp0pt, hSecV0, hI0val]; rfl
  have hL2' : L2 = encRU2 W2 (T.cfFold1 U u π cfU cu0 cπ0) ++ encIU2 W2 cu1 ++
      pr (coordsOf W2 cπ1) := by
    have := chalList_enc W2 h32 hp2b hp2e ho1a_canon hAO1 hnO1Ec hnO1Wc I1 hI1canon hAI1 hn1'c hnp1c
    rw [hsecO1, hO1val, hI1val, hcp1pt] at this
    exact this
  have hc3' : c3 = (chalStep sp (sec1C W2 sp dT T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0
      cπ0).2 (encRU2 W2 (T.cfFold1 U u π cfU cu0 cπ0) ++ encIU2 W2 cu1 ++
        pr (coordsOf W2 cπ1))).1 := by
    rw [hc3, hL2']
    unfold sec1C
    rw [← hS1', ← hL1']
  have hnat3 : natVal 128 (fun j => decide (rb1 j = 1)) =
      T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 := by
    show natVal 128 (fun j => decide (cbN cb3 j = 1)) = _
    rw [cbN_val hpm hcb3, hch2b]
    unfold ch2bnC
    have hf : T.cfFold1 U u π cfU cu0 cπ0 = foldInstance
        ((ch2anC W2 sp dT T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : ZMod p2)
        cπ0 cfU cu0 := by
      unfold Setup.cfFold1; rw [hch2a]
    rw [← hf, hc3']
  have hO2val : SecVar.val (p2 := p2) W2 O2 = T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1 := by
    rw [hO2v, hnat3, hcp1pt]
    try rw [hsecO1]
    rw [hO1val, hI1val]; rfl
  -- the output hash
  have hi1 : ((i + 1 : ℕ) : ZMod p1) = ((i : ℕ) : ZMod p1) + 1 := by push_cast; ring
  by_cases hi : i = 0
  · have hv0i : v.i = 0 := by show ((i : ℕ) : ZMod p1) = 0; rw [hi]; simp
    have e := aug_uux_zero W2 EA sp dS dT pm1 G StepRel hp hp2 hp2pos hv0i hrel
    unfold Setup.augOut
    rw [if_pos hi, if_pos hi, hi1, hhs]
    have hd : T.rawOf (dummyRU (ZMod p1) W1.toAffine.Point 1) = ⟨(0, 0), 0, (0, 0), fun _ => 0⟩ := by
      simp [Setup.rawOf, hco, dummyRU, coordsOf]
    rw [hd]
    exact e
  · have hvi : v.i ≠ 0 := fun h => hi (hcast h)
    have e := aug_uux_pos W2 EA sp dS dT pm1 G StepRel hsmul2 h2 hnr hord hrn hp hp2 hp2' hG hpm
      hvi hrel
    have hρ' : T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) = rhoOf cb := by
      unfold Setup.ch1; exact hrho1.symm
    have hF1u : F1.u = U.u + rhoOf cb := by
      rw [hF1]; unfold Setup.fold1; simp only [foldInstance]; rw [hρ']
    have hF1x : F1.x = fun _ => U.x 0 + rhoOf cb * v.uxIn := by
      rw [hF1]; unfold Setup.fold1; simp only [foldInstance]; rw [hρ']
      funext j; rw [Subsingleton.elim j 0]; simp [hux']
    have hraw : T.rawOf F1 = (⟨(vE v 8, vE v 9), v.Uu + rhoOf v.cb, (vE v 10, vE v 11),
        fun _ => v.Ux + rhoOf v.cb * v.uxIn⟩ : RawRU (ZMod p1) (ZMod p2 × ZMod p2)) := by
      simp only [Setup.rawOf, hco', hvE_eq, cs8, cs9, cs10, cs11, hF1u, hF1x, Prod.mk.eta]
      rfl
    unfold Setup.augOut
    rw [if_neg hi, if_neg hi, hi1, hhs, e, hraw, ← hO2val]
    show _ = hsC (p2 := p2) W2 sp dS v.pp (v.i + 1) v.z0 v.nx _ (SecVar.val (p2 := p2) W2 (secOf o2a O2.cmE O2.cmW))
    rw [hsecO2]

/-- **`AugComplete`, derived from the augmented circuit.**

Trusted: the completeness direction of the R1CS synthesis, `AugRel ⇒ ∃ w, Sat` (every Rust
constraint is either modelled in `AugRel` or determined by the modelled wires). -/
theorem augComplete_of_circuit
    (T : Setup (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hch2a : T.ch2an = ch2anC W2 sp dT) (hch2b : T.ch2bn = ch2bnC W2 sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstepc : ∀ z, StepRel z (T.step z)) (hEA : EA.Complete)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (hcompl : ∀ (x : Fin 1 → ZMod p1) (ω : AugVars p1 sN),
      AugRel W2 EA sp dS dT pm1 G StepRel ω (x 0) → ∃ w, T.k1.r1cs.Sat x w)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hp1b : p1 ≤ 2 ^ 254) (hp2b : p2 ≤ 2 ^ 254)
    (hG : W2.toAffine.Equation G.1 G.2) (hpm : natVal 254 pm1 = p1 - 1) :
    T.AugComplete := by
  intro i z0 zi U u π cfU cu0 cu1 cπ0 cπ1 hcast hi0 hux hx0 hx1
  obtain ⟨v, uux, hrel, huux⟩ := aug_witness W1 W2 EA sp dS dT pm1 G StepRel T hco hhs hch hch2a
    hch2b hcfx hstepc hEA hsmul2 h2 hnr hord hrn hp hp2 hp2' hp1b hp2b hG hpm i z0 zi U u π cfU
    cu0 cu1 cπ0 cπ1 hcast hi0 hux hx0 hx1
  obtain ⟨w, hw⟩ := hcompl (fun _ => uux) v hrel
  exact ⟨⟨w, 0⟩, ⟨T.k1.ckW.commit w 0, fun _ => uux⟩, ⟨hw, rfl⟩, by rw [huux]⟩

end Main

end Gadget
end Sonobe
