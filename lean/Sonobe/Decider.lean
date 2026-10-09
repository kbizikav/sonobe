import Sonobe.IVC.Soundness
import Sonobe.Snark.LegoGroth16

/-!
The CycleFold-based decider (compressor), modelled on
`CycleFoldBasedIVCDeciderCircuit::generate_constraints` (mod.rs:829-874), the Rust verifier
(mod.rs:659-717) and the EVM verifier (`cyclefold_based_ivc_decider.sol.askama`).

The decider circuit does *not* check that the incoming pair `(w, u)` satisfies the augmented
circuit. It folds `u` into `U` inside the circuit and proves that the folded running pair `UU`
(together with the CycleFold running pair) is satisfying; the Pedersen openings of `UU` are the
committed variables of the CP-SNARK (LegoGroth16), tied to the public commitments by the link
check (`LegoGroth16.lego_complete`).

The step from "LegoGroth16 accepts" to "the decider relation holds" is the CP-SNARK knowledge
soundness, kept as the hypothesis `cpSound`. The public-input encoding (8×32-bit limbs of the
commitment coordinates) and the canonicity of the contract's inputs are part of that hypothesis.
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] (T : Setup F1 G1 F2 G2 S)

/-- The relation proved by the decider circuit (mod.rs:837-873), `i ≠ 0`. -/
def Setup.DeciderRel (i : ℕ) (z0 zi : S) : Prop :=
  i ≠ 0 ∧ ∃ (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (WW : RunningWitness F1 T.m1 T.nw1) (cfU : RunningInstance F2 G2 T.l2)
    (cfW : RunningWitness F2 T.m2 T.nw2),
    u.x = (fun _ => T.hs i z0 zi U cfU) ∧ T.k1.Running (T.fold1 U u π) WW ∧ T.k2.Running cfU cfW

/-- What the decider (Rust `verify` / the contract) accepts: `i = 0` needs only `z₀ = z₀`, otherwise
the CP-SNARK proof must verify. -/
def DeciderAccept (CPVerify : ℕ → S → S → Prop) (i : ℕ) (z0 zi : S) : Prop :=
  if i = 0 then z0 = zi else CPVerify i z0 zi

/-- **Decider completeness** (relation level): every honest IVC proof yields a satisfying decider
witness. -/
theorem decider_rel_complete {n : ℕ} {z0 zn : S} {P : Proof T} (hP : T.Good (n + 1) z0 zn P) :
    T.DeciderRel (n + 1) z0 zn := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  set π := T.k1.ckE.commit (crossTerm T.k1 P.U P.W P.u P.w) 0
  exact ⟨by omega, P.U, P.u, π,
    foldWitness (T.ch1 P.U P.u π) 0 (crossTerm T.k1 P.U P.W P.u P.w) P.W P.w, P.cfU, P.cfW, hx,
    fold_complete T.k1 hU hu (T.ch1 P.U P.u π) 0, hcf⟩

/-- **Decider soundness** (relation level): a satisfying decider witness certifies
`zᵢ = Fⁱ(z₀)`. The primary instance `u` is not checked by the circuit directly; its
satisfiability is extracted from the folded pair (`Fork1` + `fold_sound`). -/
theorem decider_rel_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {i : ℕ} {z0 zi : S} (h : T.DeciderRel i z0 zi) : zi = T.step^[i] z0 := by
  obtain ⟨hi, U, u, π, WW, cfU, cfW, hux, hrun, hcf⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨_, _, _, V₁, V₂, V₃, m12, m13, m23, o1, o2, o3⟩ := f1 U u π WW hrun
  obtain ⟨W, w, hW, hw⟩ := fold_sound T.k1 hE1 hW1 U u π m12 m13 m23 o1 o2 o3
  exact ivc_sound T hA hC hH hE1 hW1 hE2 hW2 f1 f2 z0 n zi ⟨W, U, w, u, cfW, cfU⟩
    ⟨hux, hW, hw, hcf⟩

/-- **End-to-end decider soundness**: if the CP-SNARK is knowledge-sound for the decider relation
(`cpSound`), an accepted decider proof certifies `zᵢ = Fⁱ(z₀)`. -/
theorem decider_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    (CPVerify : ℕ → S → S → Prop)
    (cpSound : ∀ i z0 zi, i ≠ 0 → CPVerify i z0 zi → T.DeciderRel i z0 zi)
    {i : ℕ} {z0 zi : S} (h : DeciderAccept CPVerify i z0 zi) : zi = T.step^[i] z0 := by
  by_cases hi : i = 0
  · subst hi; simpa [DeciderAccept] using h.symm
  · simp only [DeciderAccept, if_neg hi] at h
    exact decider_rel_sound T hA hC hH hE1 hW1 hE2 hW2 f1 f2 (cpSound i z0 zi hi h)

end IVC
end Sonobe
