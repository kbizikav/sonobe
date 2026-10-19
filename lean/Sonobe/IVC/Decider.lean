import Sonobe.IVC.Soundness

/-!
The CycleFold-based decider (compressor) at the coordinate level: the decider circuit
(`CycleFoldBasedIVCDeciderCircuit::generate_constraints`, mod.rs:829-874) folds the incoming
instance into the running one *in the circuit* and proves the folded pair satisfying; it never checks
`(w, u)` against the augmented circuit directly.

The step "the verifier accepts ⇒ the decider relation holds" is derived in `FinalDecider.lean` from
the decider circuit and the contract.
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- The values of the decider circuit's witness that its relation speaks about: the instances
`U`, `u`, the cross-term commitment `π`, the folded witness `WW`, and the secondary pair. -/
structure Setup.DecOut where
  U : RunningInstance F1 G1 1
  u : IncomingInstance G1 F1 1
  π : G1
  WW : RunningWitness F1 T.m1 T.nw1
  cfU : RunningInstance F2 G2 l2
  cfW : RunningWitness F2 T.m2 T.nw2

/-- The relation proved by the decider circuit, for `n ≥ 1` steps. -/
def Setup.DeciderRel (n : ℕ) (z0 zn : S) (D : T.DecOut) : Prop :=
  n ≠ 0 ∧ D.u.x = (fun _ => T.hs T.pph (n : F1) z0 zn (T.rawOf D.U) D.cfU) ∧
    T.k1.Running (T.fold1 D.U D.u D.π) D.WW ∧ T.k2.Running D.cfU D.cfW

/-- The challenge of the decider's fold. -/
def Setup.decCh (D : T.DecOut) : F1 := T.ch1 T.pph (T.rawOf D.U) (T.rawOfI D.u) (T.coords D.π)

/-- The IVC proof the decider's fold extracts to, from a rewinding `r` of that fold. -/
def Setup.decProof (D : T.DecOut) (r : Rewind F1 T.m1 T.nw1) : Proof T :=
  ⟨(r.extract (T.decCh D) D.WW).1, D.U, (r.extract (T.decCh D) D.WW).2, D.u, D.cfW, D.cfU⟩

/-- The extraction data behind an accepted decider proof: the rewinding of the decider's fold, and
the rewindings of every step's folds (from the last step back). -/
structure Setup.Extraction where
  top : Rewind F1 T.m1 T.nw1
  steps : List T.StepData

variable (dec : (Fin T.nw1 → F1) → AugOut F1 F2 G2 S C1 l2)

/-- **The run's hypotheses for a decider proof**: every rewinding in `E` is accepting and breaks
no binding, and the hash does not collide at any step (`RunOK`). -/
def Setup.ExtractionOK (n : ℕ) (z0 zn : S) (D : T.DecOut) (E : T.Extraction) : Prop :=
  E.top.Accepts T.k1 D.U D.u D.π (T.decCh D) ∧ E.top.Binds T.k1 (T.decCh D) D.WW ∧
    T.RunOK dec z0 n zn (T.decProof D E.top) E.steps

/-- **Decider completeness (relation level)**: an accepted proof whose run meets `RunOK` gives a
decider relation, and an honest rewinding of the decider's fold gives extraction data meeting
`ExtractionOK`. -/
theorem decider_complete (h21 : (2 : F1) ≠ 0) {n : ℕ} {z0 zn : S} {P : Proof T}
    {ds : List T.StepData} (hn : n ≠ 0) (hP : T.Good n z0 zn P)
    (hrun : T.RunOK dec z0 n zn P ds) :
    ∃ (D : T.DecOut) (E : T.Extraction), T.DeciderRel n z0 zn D ∧
      T.ExtractionOK dec n z0 zn D E := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  set π := T.k1.ckE.commit (crossTerm T.k1 P.U P.W P.u P.w) 0
  set ρ := T.ch1 T.pph (T.rawOf P.U) (T.rawOfI P.u) (T.coords π)
  obtain ⟨r, ha, hb, he⟩ := Rewind.exists_honest T.k1 hU hu 0 (exists_two_ne h21 ρ)
  set D : T.DecOut :=
    ⟨P.U, P.u, π, foldWitness ρ 0 (crossTerm T.k1 P.U P.W P.u P.w) P.W P.w, P.cfU, P.cfW⟩
  have hdp : T.decProof D r = P := by
    have he' : r.extract (T.decCh D) D.WW = (P.W, P.w) := he
    rw [Setup.decProof, he']
  refine ⟨D, ⟨r, ds⟩, ⟨hn, hx, fold_complete T.k1 hU hu ρ 0, hcf⟩, ha, hb, ?_⟩
  show T.RunOK dec z0 n zn (T.decProof D r) ds
  rw [hdp]
  exact hrun

variable {SW : Type*} {R : S → SW → S → Prop}

/-- **Decider soundness (relation level).** -/
theorem decider_rel_sound (hA : T.AugSound R dec) (hC : T.CFSound) {N : ℕ}
    (hcast : CastOK F1 N) {n : ℕ} (hn : n ≤ N) {z0 zn : S} {D : T.DecOut}
    (h : T.DeciderRel n z0 zn D) (E : T.Extraction) (hE : T.ExtractionOK dec n z0 zn D E) :
    ∃ ws : List SW, ws.length = n ∧ Chain R z0 ws zn := by
  obtain ⟨hn0, hux, hrun, hcf⟩ := h
  obtain ⟨ha, hb, hruns⟩ := hE
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hrun' : T.k1.Running (foldInstance (T.decCh D) D.π D.U D.u) D.WW := hrun
  obtain ⟨hW, hw⟩ := Rewind.sound T.k1 hrun' ha hb
  have hP : T.Good (m + 1) z0 zn (T.decProof D E.top) := ⟨hux, hW, hw, hcf⟩
  exact ivc_sound T dec hA hC hcast z0 m hn zn (T.decProof D E.top) E.steps hP hruns

end IVC
end Sonobe
