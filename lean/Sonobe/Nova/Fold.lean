import Sonobe.Arith.R1CS
import Sonobe.Commitment.Pedersen

/-!
Nova (1,1) folding, modelled on `crates/fs/src/nova/{instances,witnesses,keys}` and
`algorithms/{prover,verifier}.rs`. Two commitment keys are used (witness / error); sonobe shares one
key of length `≥ max(m, nw)` — a specialisation of this model.
-/

namespace Sonobe
namespace Nova

open R1CS

variable {F G : Type*} [CommRing F] [AddCommGroup G] [Module F G] {m l nw : ℕ}

/-- `RunningInstance` (instances/mod.rs:16). -/
structure RunningInstance (F G : Type*) (l : ℕ) where
  cmE : G
  u : F
  cmW : G
  x : Fin l → F

/-- `RunningWitness` (witnesses/mod.rs:14). -/
structure RunningWitness (F : Type*) (m nw : ℕ) where
  e : Fin m → F
  rE : F
  w : Fin nw → F
  rW : F

/-- `IncomingInstance` / `IncomingWitness`. -/
structure IncomingInstance (G F : Type*) (l : ℕ) where
  cmW : G
  x : Fin l → F

structure IncomingWitness (F : Type*) (nw : ℕ) where
  w : Fin nw → F
  rW : F

/-- Decider key: shape + commitment keys (keys/mod.rs:26). -/
structure Key (F G : Type*) [CommRing F] [AddCommGroup G] [Module F G] (m l nw : ℕ) where
  r1cs : R1CS F m l nw
  ckE : PedersenKey F G m
  ckW : PedersenKey F G nw

/-- Committed relaxed R1CS (keys/mod.rs:48). -/
def Key.Running (k : Key F G m l nw) (U : RunningInstance F G l) (W : RunningWitness F m nw) :
    Prop :=
  k.r1cs.RelaxedSat U.u U.x W.w W.e ∧ k.ckE.Opens W.e W.rE U.cmE ∧ k.ckW.Opens W.w W.rW U.cmW

/-- Committed plain R1CS (keys/mod.rs:66). -/
def Key.Incoming (k : Key F G m l nw) (u : IncomingInstance G F l) (w : IncomingWitness F nw) :
    Prop :=
  k.r1cs.Sat u.x w.w ∧ k.ckW.Opens w.w w.rW u.cmW

/-- Cross term `T = R1CS(z₁+z₂) − e₁ − e₂` with `e₂ = 0` (prover.rs:21). -/
def crossTerm (k : Key F G m l nw) (U : RunningInstance F G l) (W : RunningWitness F m nw)
    (u : IncomingInstance G F l) (w : IncomingWitness F nw) : Fin m → F :=
  k.r1cs.eval (zvec (U.u + 1) (U.x + u.x) (W.w + w.w)) - W.e

/-- Prover fold (prover.rs:52); `rT` is the opening randomness of `cm_t`. -/
def foldWitness (ρ rT : F) (T : Fin m → F) (W : RunningWitness F m nw)
    (w : IncomingWitness F nw) : RunningWitness F m nw where
  e := W.e + ρ • T
  rE := W.rE + ρ * rT
  w := W.w + ρ • w.w
  rW := W.rW + ρ * w.rW

/-- Verifier fold (verifier.rs:15). -/
def foldInstance (ρ : F) (cmT : G) (U : RunningInstance F G l) (u : IncomingInstance G F l) :
    RunningInstance F G l where
  cmE := U.cmE + ρ • cmT
  u := U.u + ρ
  cmW := U.cmW + ρ • u.cmW
  x := U.x + ρ • u.x

/-- **Completeness of the Nova fold**: for any challenge `ρ`, folding a satisfying running pair with a
satisfying incoming pair gives a satisfying running pair. -/
theorem fold_complete (k : Key F G m l nw) {U W u w} (hU : k.Running U W) (hu : k.Incoming u w)
    (ρ rT : F) :
    k.Running (foldInstance ρ (k.ckE.commit (crossTerm k U W u w) rT) U u)
      (foldWitness ρ rT (crossTerm k U W u w) W w) := by
  obtain ⟨hr, hE, hW⟩ := hU
  obtain ⟨hs, hW'⟩ := hu
  have hz := zvec_fold U.u ρ U.x u.x W.w w.w
  refine ⟨?_, ?_, ?_⟩
  · simp only [RelaxedSat, foldInstance, foldWitness, hz, R1CS.eval_fold]
    have h1 : k.r1cs.eval (zvec U.u U.x W.w) = W.e := hr
    have h2 : k.r1cs.eval (zvec 1 u.x w.w) = 0 := hs
    have h3 : zvec U.u U.x W.w + zvec 1 u.x w.w = zvec (U.u + 1) (U.x + u.x) (W.w + w.w) :=
      (zvec_add _ _ _ _ _ _).symm
    rw [h1, h2, h3]
    simp [crossTerm]
  · unfold PedersenKey.Opens at *
    simp only [foldInstance, foldWitness, PedersenKey.commit_fold, hE]
  · unfold PedersenKey.Opens at *
    simp only [foldInstance, foldWitness, PedersenKey.commit_fold, hW, hW']

end Nova
end Sonobe
