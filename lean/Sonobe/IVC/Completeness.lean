import Sonobe.IVC.Soundness

/-!
IVC completeness at the coordinate level: an honest prover, running the folding schemes and the
(specified) circuits, always produces a proof the verifier accepts (mod.rs:310-421 against
mod.rs:431-477), and its run meets the hypotheses of soundness: honest rewindings of every fold
give extraction data meeting `RunOK`.

The circuits are kept behind `AugComplete` and `CFComplete`, the completeness counterparts of
`AugSound` and `CFSound`.
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- First secondary fold of a step (verifier side): the challenge is derived from the transcript,
which contains the primary data. -/
def Setup.cfFold1 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 : IncomingInstance G2 F2 l2) (cπ0 : G2) :
    RunningInstance F2 G2 l2 :=
  foldInstance ((T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : F2) cπ0
    cfU cu0

/-- Second secondary fold of a step. -/
def Setup.cfFold2 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 : IncomingInstance G2 F2 l2) (cπ0 : G2)
    (cu1 : IncomingInstance G2 F2 l2) (cπ1 : G2) : RunningInstance F2 G2 l2 :=
  foldInstance ((T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 : ℕ) : F2)
    cπ1 (T.cfFold1 U u π cfU cu0 cπ0) cu1

/-- Public output of the augmented circuit (circuits.rs:187-194): `H(pp, i+1, z₀, z_{i+1}, UU, cf_UU)`
with the dummies selected in the base case. -/
def Setup.augOut (i : ℕ) (z0 nx : S) (U : RunningInstance F1 G1 1)
    (u : IncomingInstance G1 F1 1) (π : G1) (cfU : RunningInstance F2 G2 l2)
    (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) : F1 :=
  T.hs T.pph ((i + 1 : ℕ) : F1) z0 nx
    (if i = 0 then T.rawOf (dummyRU F1 G1 1) else T.rawOf (T.fold1 U u π))
    (if i = 0 then dummyRU F2 G2 l2 else T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1)

/-- The values the honest assignment of the augmented circuit carries: the step's inputs, the
honest CycleFold instances and proofs, the challenges of the two secondary folds, and the
coordinates of the folded primary commitments. -/
def Setup.honestOut (i : ℕ) (z0 zi nx : S) (U : RunningInstance F1 G1 1)
    (u : IncomingInstance G1 F1 1) (π : G1) (cfU : RunningInstance F2 G2 l2)
    (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) : AugOut F1 F2 G2 S C1 l2 :=
  ⟨T.pph, (i : F1), z0, zi, nx, T.rawOf U, T.rawOfI u, T.coords π, cfU, cu0, cu1, cπ0, cπ1,
    ((T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : F2),
    ((T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 : ℕ) : F2),
    T.coords (T.fold1 U u π).cmE, T.coords (T.fold1 U u π).cmW⟩

/-- Circuit completeness: for a step `R zᵢ w z_{i+1}` and the honest CycleFold inputs, the augmented
circuit has a satisfying assignment, whose public input is `augOut` and whose values, read off by
`dec`, are the honest ones. -/
def Setup.AugComplete {SW : Type*} (R : S → SW → S → Prop)
    (dec : (Fin T.nw1 → F1) → AugOut F1 F2 G2 S C1 l2) : Prop :=
  ∀ (i : ℕ) (z0 zi nx : S) (sw : SW) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1)
    (π : G1) (cfU : RunningInstance F2 G2 l2) (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2),
    R zi sw nx → (((i : ℕ) : F1) = 0 → i = 0) → (i = 0 → z0 = zi) →
    u.x = (fun _ => T.hs T.pph (i : F1) z0 zi (T.rawOf U) cfU) →
    cu0.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmE)
      (T.coords π) (T.coords (T.fold1 U u π).cmE) →
    cu1.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmW)
      (T.coords u.cmW) (T.coords (T.fold1 U u π).cmW) →
    ∃ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1),
      T.k1.Incoming u' w' ∧ u'.x = (fun _ => T.augOut i z0 nx U u π cfU cu0 cu1 cπ0 cπ1) ∧
      dec w'.w = T.honestOut i z0 zi nx U u π cfU cu0 cu1 cπ0 cπ1

/-- CycleFold circuit completeness: `P₂ = P₀ + ρ P₁` is satisfiable with public input `cfX`. -/
def Setup.CFComplete : Prop :=
  ∀ (n : ℕ) (P0 P1 P2 : G1), n < 2 ^ 128 → P2 = P0 + (n : F1) • P1 →
    ∃ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 l2),
      T.k2.Incoming cu cw ∧ cu.x = T.cfX n (T.coords P0) (T.coords P1) (T.coords P2)

/-- `IVCVerifier::verify` (mod.rs:431), after the shape checks. -/
def Setup.Verify (i : ℕ) (z0 zi : S) (P : Proof T) : Prop :=
  if i = 0 then z0 = zi else T.Good i z0 zi P

theorem Setup.outU_honestOut {i : ℕ} (hcast : ((i : ℕ) : F1) = 0 → i = 0) (z0 zi nx : S)
    (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) :
    T.outU (T.honestOut i z0 zi nx U u π cfU cu0 cu1 cπ0 cπ1) =
      if i = 0 then T.rawOf (dummyRU F1 G1 1) else T.rawOf (T.fold1 U u π) := by
  by_cases hi : i = 0
  · subst hi; simp [Setup.outU, Setup.honestOut]
  · have h : ((i : ℕ) : F1) ≠ 0 := fun h => hi (hcast h)
    simp only [Setup.outU, Setup.honestOut, if_neg h, if_neg hi]
    rfl

theorem Setup.outCf_honestOut {i : ℕ} (hcast : ((i : ℕ) : F1) = 0 → i = 0) (z0 zi nx : S)
    (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) :
    (T.honestOut i z0 zi nx U u π cfU cu0 cu1 cπ0 cπ1).outCf =
      if i = 0 then dummyRU F2 G2 l2 else T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1 := by
  by_cases hi : i = 0
  · subst hi; simp [AugOut.outCf, Setup.honestOut]
  · have h : ((i : ℕ) : F1) ≠ 0 := fun h => hi (hcast h)
    simp only [AugOut.outCf, Setup.honestOut, if_neg h, if_neg hi]
    rfl

theorem Setup.inU_honestOut (i : ℕ) (z0 zi nx : S) (U : RunningInstance F1 G1 1)
    (u : IncomingInstance G1 F1 1) (π : G1) (cfU : RunningInstance F2 G2 l2)
    (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) :
    T.inU (T.honestOut i z0 zi nx U u π cfU cu0 cu1 cπ0 cπ1) = U := by
  simp only [Setup.inU, Setup.honestOut, Setup.rawOf, Setup.pt_coords]

theorem Setup.inu_honestOut (i : ℕ) (z0 zi nx : S) (U : RunningInstance F1 G1 1)
    (u : IncomingInstance G1 F1 1) (π : G1) (cfU : RunningInstance F2 G2 l2)
    (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) :
    T.inu (T.honestOut i z0 zi nx U u π cfU cu0 cu1 cπ0 cπ1) = u := by
  simp only [Setup.inu, Setup.honestOut, Setup.rawOfI, Setup.pt_coords]

variable (dec : (Fin T.nw1 → F1) → AugOut F1 F2 G2 S C1 l2)
variable {SW : Type*} {R : S → SW → S → Prop}

/-- Base case `i = 0` (mod.rs:358 skipped; the circuit runs on dummies). -/
theorem prove_base (hA : T.AugComplete R dec) (hC : T.CFComplete) {z0 z1 : S} {sw : SW}
    (hR : R z0 sw z1) : ∃ P : Proof T, T.Good 1 z0 z1 P ∧ T.HashOK dec 1 z0 z1 P := by
  set U := dummyRU F1 G1 1 with hU0
  set cfU := dummyRU F2 G2 l2 with hcfU0
  set u : IncomingInstance G1 F1 1 :=
    ⟨0, fun _ => T.hs T.pph (((0 : ℕ)) : F1) z0 z0 (T.rawOf U) cfU⟩ with hu
  obtain ⟨cw0, cu0, -, hx0⟩ := hC (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords 0)) U.cmE 0
    (T.fold1 U u 0).cmE (T.ch1n_small _ _ _ _) rfl
  obtain ⟨cw1, cu1, -, hx1⟩ := hC (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords 0)) U.cmW
    u.cmW (T.fold1 U u 0).cmW (T.ch1n_small _ _ _ _) rfl
  obtain ⟨w', u', hu', hxu', hdec⟩ :=
    hA 0 z0 z0 z1 sw U u 0 cfU cu0 cu1 0 0 hR (fun _ => rfl) (fun _ => rfl) rfl hx0 hx1
  refine ⟨⟨dummyRW F1 T.m1 T.nw1, U, w', u', dummyRW F2 T.m2 T.nw2, cfU⟩,
    ⟨?_, running_dummy _, hu', running_dummy _⟩, ?_⟩
  · simp [hxu', Setup.augOut]
    rfl
  · show T.HsAt T.pph ((1 : ℕ) : F1) z0 z1 (T.rawOf U) cfU (dec w'.w).pp ((dec w'.w).i + 1)
      (dec w'.w).z0 (dec w'.w).nx (T.outU (dec w'.w)) (dec w'.w).outCf
    rw [hdec, T.outU_honestOut (fun _ => rfl), T.outCf_honestOut (fun _ => rfl)]
    intro _
    simp [Setup.honestOut, hU0, hcfU0]

/-- One honest prover step from a satisfying `(U, W, u, w, cf_U, cf_W)` (`n ≥ 1`), with the honest
rewindings of its folds: the step back extracts the proof it started from. -/
theorem prove_succ (hA : T.AugComplete R dec) (hC : T.CFComplete) (h21 : (2 : F1) ≠ 0)
    (h22 : (2 : F2) ≠ 0) (n : ℕ) (hnc : ((n : ℕ) : F1) ≠ 0) (z0 zn : S) {zn' : S} {sw : SW}
    (hR : R zn sw zn') (P : Proof T) (hP : T.Good n z0 zn P) :
    ∃ (P' : Proof T) (d : T.StepData), T.Good (n + 1) z0 zn' P' ∧ T.HashOK dec (n + 1) z0 zn' P' ∧
      T.ForkOK dec P' d ∧ (dec P'.w.w).zi = zn ∧ T.back dec P' d = P := by
  have hn : n ≠ 0 := fun h => hnc (by rw [h]; simp)
  have hcast : ((n : ℕ) : F1) = 0 → n = 0 := fun h => absurd h hnc
  obtain ⟨hxu, hU, hu, hcf⟩ := hP
  set U := P.U; set W := P.W; set u := P.u; set w := P.w; set cfU := P.cfU; set cfW := P.cfW
  -- primary fold
  set π := T.k1.ckE.commit (crossTerm T.k1 U W u w) 0 with hπ
  set ρ := T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) with hρ
  have hUU := fold_complete T.k1 hU hu ρ 0
  -- the two CycleFold circuits
  obtain ⟨cw0, cu0, hcu0, hx0⟩ := hC _ U.cmE π (T.fold1 U u π).cmE (T.ch1n_small _ _ _ _) rfl
  obtain ⟨cw1, cu1, hcu1, hx1⟩ := hC _ U.cmW u.cmW (T.fold1 U u π).cmW (T.ch1n_small _ _ _ _) rfl
  set cπ0 := T.k2.ckE.commit (crossTerm T.k2 cfU cfW cu0 cw0) 0 with hcπ0
  set ρ0 : F2 := ((T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : F2)
    with hρ0
  have hf0 := fold_complete T.k2 hcf hcu0 ρ0 0
  set cfU1 := T.cfFold1 U u π cfU cu0 cπ0 with hcfU1
  set cfW1 := foldWitness ρ0 0 (crossTerm T.k2 cfU cfW cu0 cw0) cfW cw0
  set cπ1 := T.k2.ckE.commit (crossTerm T.k2 cfU1 cfW1 cu1 cw1) 0
  set ρ1 : F2 := ((T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 : ℕ) : F2)
    with hρ1
  have hf1 := fold_complete T.k2 hf0 hcu1 ρ1 0
  obtain ⟨w', u', hu', hxu', hdec⟩ := hA n z0 zn zn' sw U u π cfU cu0 cu1 cπ0 cπ1 hR
    (fun h => absurd h hnc) (fun h => absurd h hn) hxu hx0 hx1
  -- the honest rewindings
  obtain ⟨r1, a1, b1, e1⟩ := Rewind.exists_honest T.k1 hU hu 0 (exists_two_ne h21 ρ)
  obtain ⟨r2a, a2a, b2a, e2a⟩ := Rewind.exists_honest T.k2 hcf hcu0 0 (exists_two_ne h22 ρ0)
  obtain ⟨r2b, a2b, b2b, e2b⟩ := Rewind.exists_honest T.k2 hf0 hcu1 0 (exists_two_ne h22 ρ1)
  set P' : Proof T := ⟨foldWitness ρ 0 (crossTerm T.k1 U W u w) W w, T.fold1 U u π, w', u',
    foldWitness ρ1 0 (crossTerm T.k2 cfU1 cfW1 cu1 cw1) cfW1 cw1,
    T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1⟩ with hP'
  set d : T.StepData := ⟨r1, r2a, r2b⟩ with hd
  set o := T.honestOut n z0 zn zn' U u π cfU cu0 cu1 cπ0 cπ1 with ho
  have hdec' : dec P'.w.w = o := hdec
  have hX : (T.ext2b dec P' d).1 = cfW1 := by
    show (r2b.extract (dec P'.w.w).cρ1 P'.cfW).1 = cfW1
    rw [hdec']
    exact congrArg Prod.fst e2b
  refine ⟨P', d, ⟨?_, hUU, hu', hf1⟩, ?_, ?_, ?_, ?_⟩
  · simp [hP', hn, hxu', Setup.augOut]
  · show T.HsAt T.pph ((n + 1 : ℕ) : F1) z0 zn' (T.rawOf (T.fold1 U u π))
      (T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1) (dec P'.w.w).pp ((dec P'.w.w).i + 1)
      (dec P'.w.w).z0 (dec P'.w.w).nx (T.outU (dec P'.w.w)) (dec P'.w.w).outCf
    rw [hdec', ho, T.outU_honestOut hcast, T.outCf_honestOut hcast]
    intro _
    simp [Setup.honestOut, hn]
  · simp only [Setup.ForkOK]
    rw [hX, hdec', ho, T.inU_honestOut, T.inu_honestOut]
    exact ⟨a2b, b2b, a2a, b2a, by simp only [Setup.honestOut, Setup.pt_coords]; exact a1, b1⟩
  · rw [hdec', ho]; rfl
  · simp only [Setup.back]
    rw [hX, hdec']
    have e1' : d.r1.extract (T.chOf o) P'.W = (W, w) := e1
    have e2a' : d.r2a.extract o.cρ0 cfW1 = (cfW, cw0) := e2a
    rw [e1', e2a', ho, T.inU_honestOut, T.inu_honestOut]
    rfl

/-- **IVC completeness**: for every chain of `n ≤ N` steps (step counts that are non-zero in the
field) there is an accepting proof of `(n, z₀, zₙ)`, and for `n ≥ 1` extraction data of its run
meeting `RunOK`. -/
theorem ivc_complete (hA : T.AugComplete R dec) (hC : T.CFComplete) (h21 : (2 : F1) ≠ 0)
    (h22 : (2 : F2) ≠ 0) {N : ℕ} (hcast : CastOK F1 N) (z0 : S) :
    ∀ (ws : List SW) (zn : S), Chain R z0 ws zn → ws.length ≤ N →
      ∃ (P : Proof T) (ds : List T.StepData), T.Verify ws.length z0 zn P ∧
        (ws ≠ [] → T.RunOK dec z0 ws.length zn P ds) := by
  have good : ∀ (ws : List SW) (zn : S), Chain R z0 ws zn → ws ≠ [] → ws.length ≤ N →
      ∃ (P : Proof T) (ds : List T.StepData), T.Good ws.length z0 zn P ∧
        T.RunOK dec z0 ws.length zn P ds := by
    intro ws
    induction ws using List.reverseRecOn with
    | nil => intro _ _ h; exact absurd rfl h
    | append_singleton ws sw ih =>
      intro zn hc _ hN
      obtain ⟨zm, hcm, hR⟩ := Chain.of_snoc hc
      by_cases hne : ws = []
      · subst hne
        cases hcm
        obtain ⟨P, hP, hH⟩ := prove_base T dec hA hC hR
        exact ⟨P, [], hP, hH⟩
      · obtain ⟨P, ds, hP, hrun⟩ := ih zm hcm hne (by simp at hN; omega)
        obtain ⟨k, hk⟩ : ∃ k, ws.length = k + 1 :=
          ⟨ws.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
        have hl : ws.length ≠ 0 := by omega
        obtain ⟨P', d, hP', hH, hF, hzi, hback⟩ := prove_succ T dec hA hC h21 h22 ws.length
          (fun h => hl (hcast _ (by simp at hN; omega) h)) z0 zm hR P hP
        refine ⟨P', d :: ds, by simpa using hP', ?_⟩
        rw [List.length_append, List.length_singleton, hk]
        rw [hk] at hH hrun
        refine ⟨hH, hF, ?_⟩
        rw [hzi, hback]
        exact hrun
  intro ws zn hc hN
  by_cases hne : ws = []
  · subst hne
    cases hc
    exact ⟨⟨dummyRW F1 T.m1 T.nw1, dummyRU F1 G1 1, ⟨0, 0⟩, ⟨0, fun _ => 0⟩,
      dummyRW F2 T.m2 T.nw2, dummyRU F2 G2 l2⟩, [], by simp [Setup.Verify], fun h => absurd rfl h⟩
  · obtain ⟨P, ds, hP, hrun⟩ := good ws zn hc hne hN
    exact ⟨P, ds, by simpa [Setup.Verify, List.length_eq_zero_iff, hne] using hP, fun _ => hrun⟩

end IVC
end Sonobe
