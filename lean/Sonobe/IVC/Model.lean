import Sonobe.Nova.Fold

/-!
Nova + CycleFold IVC, modelled on `crates/ivc/src/compilers/cyclefold/{mod,circuits}.rs`.

Everything about the *augmented circuit* and the *CycleFold circuit* is kept behind two explicit
specifications (`AugComplete`/`AugSound`, `CFComplete`/`CFSound`); those are what the constraint-level
development of the gadgets (Griffin sponge, EC addition, bit decomposition) discharges.

Conventions: primary field `F1` is the transcript field and the scalar field of `G1`; secondary
`F2`/`G2` likewise. The primary augmented circuit has exactly one public input (`l1 = 1`).
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2]

/-- The all-zero instance used as `Dummy` (circuits.rs:124-128). -/
def dummyRU (F G : Type*) [Zero F] [Zero G] (l : ℕ) : RunningInstance F G l := ⟨0, 0, 0, fun _ => 0⟩
def dummyRW (F : Type*) [Zero F] (m nw : ℕ) : RunningWitness F m nw := ⟨0, 0, 0, 0⟩

theorem running_dummy {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {m l nw : ℕ}
    (k : Key F G m l nw) : k.Running (dummyRU F G l) (dummyRW F m nw) := by
  refine ⟨?_, ?_, ?_⟩
  · have : R1CS.zvec (0 : F) (fun _ : Fin l => (0 : F)) (0 : Fin nw → F) = 0 := by
      ext i; rcases i with _ | _ | _ <;> simp [R1CS.zvec]
    simp only [R1CS.RelaxedSat, dummyRU, dummyRW]
    rw [this]; simp [R1CS.eval]
  · exact PedersenKey.commit_zero _
  · exact PedersenKey.commit_zero _

structure Setup (F1 G1 F2 G2 S : Type*) [Field F1] [AddCommGroup G1] [Module F1 G1]
    [Field F2] [AddCommGroup G2] [Module F2 G2] where
  m1 : ℕ
  nw1 : ℕ
  m2 : ℕ
  l2 : ℕ
  nw2 : ℕ
  /-- augmented-circuit shape and commitment keys -/
  k1 : Key F1 G1 m1 1 nw1
  /-- CycleFold-circuit shape and commitment keys -/
  k2 : Key F2 G2 m2 l2 nw2
  step : S → S
  /-- `H(i, z₀, zᵢ, U, cf_U)` (circuits.rs:138, mod.rs:460) -/
  hs : ℕ → S → S → RunningInstance F1 G1 1 → RunningInstance F2 G2 l2 → F1
  /-- Fiat-Shamir challenges of the primary / secondary fold (abstract random oracle) -/
  ch1 : RunningInstance F1 G1 1 → IncomingInstance G1 F1 1 → G1 → F1
  ch2 : RunningInstance F2 G2 l2 → IncomingInstance G2 F2 l2 → G2 → F2
  /-- public inputs of one CycleFold circuit: `(ρ, P₀, P₁, P₂)` (adapters/nova.rs:48) -/
  cfX : F1 → G1 → G1 → G1 → Fin l2 → F2

variable (T : Setup F1 G1 F2 G2 S)

/-- Primary fold, verifier side. -/
def Setup.fold1 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1) :
    RunningInstance F1 G1 1 :=
  foldInstance (T.ch1 U u π) π U u

/-- Secondary fold, verifier side. -/
def Setup.fold2 (U : RunningInstance F2 G2 T.l2) (u : IncomingInstance G2 F2 T.l2) (π : G2) :
    RunningInstance F2 G2 T.l2 :=
  foldInstance (T.ch2 U u π) π U u

/-- Public output of the augmented circuit (circuits.rs:187-194): `H(i+1, z₀, F zᵢ, UU, cf_UU)`
with the dummies selected in the base case. -/
def Setup.augOut (i : ℕ) (z0 zi : S) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1)
    (π : G1) (cfU : RunningInstance F2 G2 T.l2) (cu0 cu1 : IncomingInstance G2 F2 T.l2)
    (cπ0 cπ1 : G2) : F1 :=
  T.hs (i + 1) z0 (T.step zi)
    (if i = 0 then dummyRU F1 G1 1 else T.fold1 U u π)
    (if i = 0 then dummyRU F2 G2 T.l2 else T.fold2 (T.fold2 cfU cu0 cπ0) cu1 cπ1)

/-- Circuit completeness: if the CycleFold inputs are the honest ones, the augmented circuit
has a satisfying assignment, whose public input is `augOut`. -/
def Setup.AugComplete : Prop :=
  ∀ (i : ℕ) (z0 zi : S) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 T.l2) (cu0 cu1 : IncomingInstance G2 F2 T.l2) (cπ0 cπ1 : G2),
    (i = 0 → z0 = zi) →
    cu0.x = T.cfX (T.ch1 U u π) U.cmE π (T.fold1 U u π).cmE →
    cu1.x = T.cfX (T.ch1 U u π) U.cmW u.cmW (T.fold1 U u π).cmW →
    ∃ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1),
      T.k1.Incoming u' w' ∧ u'.x = fun _ => T.augOut i z0 zi U u π cfU cu0 cu1 cπ0 cπ1

/-- CycleFold circuit completeness: `P₂ = P₀ + ρ P₁` is satisfiable with public input `cfX`. -/
def Setup.CFComplete : Prop :=
  ∀ (ρ : F1) (P0 P1 P2 : G1), P2 = P0 + ρ • P1 →
    ∃ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 T.l2),
      T.k2.Incoming cu cw ∧ cu.x = T.cfX ρ P0 P1 P2

/-- IVC proof `(W, U, w, u, cf_W, cf_U)` (mod.rs:126). -/
structure Proof where
  W : RunningWitness F1 T.m1 T.nw1
  U : RunningInstance F1 G1 1
  w : IncomingWitness F1 T.nw1
  u : IncomingInstance G1 F1 1
  cfW : RunningWitness F2 T.m2 T.nw2
  cfU : RunningInstance F2 G2 T.l2

/-- `IVCVerifier::verify` (mod.rs:431), after the shape checks. -/
def Setup.Verify (i : ℕ) (z0 zi : S) (P : Proof T) : Prop :=
  if i = 0 then z0 = zi else
    P.u.x = (fun _ => T.hs i z0 zi P.U P.cfU) ∧ T.k1.Running P.U P.W ∧
    T.k1.Incoming P.u P.w ∧ T.k2.Running P.cfU P.cfW

end IVC
end Sonobe
