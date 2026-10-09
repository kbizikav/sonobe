import Sonobe.IVC2.Soundness

/-!
The CycleFold-based decider (compressor) at the coordinate level: the decider circuit
(`CycleFoldBasedIVCDeciderCircuit::generate_constraints`, mod.rs:829-874) folds the incoming
instance into the running one *in the circuit* and proves the folded pair satisfying; it never checks
`(w, u)` against the augmented circuit directly.

The step "the CP-SNARK (LegoGroth16) accepts ⇒ the decider relation holds" is its knowledge
soundness, the hypothesis `cpSound`.
-/

namespace Sonobe
namespace IVC2

open Nova IVC

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup2 F1 G1 F2 G2 S C1 l2)

/-- The relation proved by the decider circuit, for `n ≥ 1` steps. -/
def Setup2.DeciderRel (n : ℕ) (z0 zn : S) : Prop :=
  n ≠ 0 ∧ ∃ (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (WW : RunningWitness F1 T.m1 T.nw1) (cfU : RunningInstance F2 G2 l2)
    (cfW : RunningWitness F2 T.m2 T.nw2),
    u.x = (fun _ => T.hs T.pph (n : F1) z0 zn (T.rawOf U) cfU) ∧
      T.k1.Running (T.fold1 U u π) WW ∧ T.k2.Running cfU cfW

/-- Acceptance of the decider: `n = 0` needs only `z₀ = zₙ`. -/
def DeciderAccept (CPVerify : ℕ → S → S → Prop) (n : ℕ) (z0 zn : S) : Prop :=
  if n = 0 then z0 = zn else CPVerify n z0 zn

/-- **Decider completeness (relation level).** -/
theorem decider_rel_complete {n : ℕ} {z0 zn : S} {P : Proof2 T} (hP : T.Good (n + 1) z0 zn P) :
    T.DeciderRel (n + 1) z0 zn := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  set π := T.k1.ckE.commit (crossTerm T.k1 P.U P.W P.u P.w) 0
  exact ⟨by omega, P.U, P.u, π,
    foldWitness (T.ch1 T.pph (T.rawOf P.U) (T.rawOfI P.u) (T.coords π)) 0
      (crossTerm T.k1 P.U P.W P.u P.w) P.W P.w, P.cfU, P.cfW, hx,
    fold_complete T.k1 hU hu _ 0, hcf⟩

/-- **Decider soundness (relation level).** -/
theorem decider_rel_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK F1 N) {n : ℕ} (hn : n ≤ N) {z0 zn : S}
    (h : T.DeciderRel n z0 zn) : zn = T.step^[n] z0 := by
  obtain ⟨hn0, U, u, π, WW, cfU, cfW, hux, hrun, hcf⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, _, _, V₁, V₂, V₃, a12, a13, a23, g1, g2, g3⟩ := f1 _ U u π WW hrun
  obtain ⟨W, w, hW, hw⟩ := fold_sound T.k1 hE1 hW1 U u π a12 a13 a23 g1 g2 g3
  exact ivc_sound T hA hC hH hE1 hW1 hE2 hW2 f1 f2 hcast z0 m hn zn ⟨W, U, w, u, cfW, cfU⟩
    ⟨hux, hW, hw, hcf⟩

/-- **End-to-end decider soundness.** -/
theorem decider_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK F1 N) (CPVerify : ℕ → S → S → Prop)
    (cpSound : ∀ n z0 zn, n ≠ 0 → CPVerify n z0 zn → T.DeciderRel n z0 zn)
    {n : ℕ} (hn : n ≤ N) {z0 zn : S} (h : DeciderAccept CPVerify n z0 zn) :
    zn = T.step^[n] z0 := by
  by_cases h0 : n = 0
  · subst h0; simpa [DeciderAccept] using h.symm
  · simp only [DeciderAccept, if_neg h0] at h
    exact decider_rel_sound T hA hC hH hE1 hW1 hE2 hW2 f1 f2 hcast hn (cpSound n z0 zn h0 h)

end IVC2
end Sonobe
