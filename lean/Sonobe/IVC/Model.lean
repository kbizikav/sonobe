import Sonobe.Nova.Soundness
import Sonobe.Nova.Fold

/-!
Coordinate-level model of the Nova + CycleFold IVC.

The primary commitments handled by the augmented circuit are *raw coordinate pairs* (`C1`): the
circuit allocates them as `EmulatedAffineVar`s with a range check but no curve check. That they are
genuine group elements follows only from the CycleFold circuit, which allocates them as curve
points; this is made explicit in `CFSound`.

The hash also takes the public-parameter hash `pph` as an argument: in the augmented circuit it is
a free witness (`FpVar::new_witness(pp_hash)`), so the verifier's hash binds it.
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
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

/-- A primary running instance whose commitments are raw coordinates. -/
structure RawRU (F C : Type*) where
  cmE : C
  u : F
  cmW : C
  x : Fin 1 → F

structure RawIU (F C : Type*) where
  cmW : C
  x : Fin 1 → F

structure Setup (F1 G1 F2 G2 S C1 : Type*) (l2 : ℕ) [Field F1] [AddCommGroup G1] [Module F1 G1]
    [Field F2] [AddCommGroup G2] [Module F2 G2] where
  m1 : ℕ
  nw1 : ℕ
  m2 : ℕ
  nw2 : ℕ
  k1 : Key F1 G1 m1 1 nw1
  k2 : Key F2 G2 m2 l2 nw2
  step : S → S
  /-- coordinates of a primary commitment (identity ↦ `(0,0)`) -/
  coords : G1 → C1
  coords_inj : Function.Injective coords
  /-- public-parameter hash -/
  pph : F1
  /-- `H(pph, i, z₀, zᵢ, U, cf_U)` (circuits.rs:138) -/
  hs : F1 → F1 → S → S → RawRU F1 C1 → RunningInstance F2 G2 l2 → F1
  /-- Fiat–Shamir challenge (an integer `< 2^128`) of the primary fold, from the raw absorbed data -/
  ch1n : F1 → RawRU F1 C1 → RawIU F1 C1 → C1 → ℕ
  /-- challenge of a secondary fold (prover side) -/
  ch2 : F1 → RunningInstance F2 G2 l2 → IncomingInstance G2 F2 l2 → G2 → F2
  /-- public inputs of one CycleFold circuit: `(ρ, P₀, P₁, P₂)` -/
  cfX : ℕ → C1 → C1 → C1 → Fin l2 → F2
  /-- the challenge is `< 2^128` -/
  ch1n_small : ∀ pp U u π, ch1n pp U u π < 2 ^ 128

variable {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- The primary challenge as a field element. -/
def Setup.ch1 (pp : F1) (U : RawRU F1 C1) (u : RawIU F1 C1) (π : C1) : F1 := (T.ch1n pp U u π : F1)

def Setup.rawOf (U : RunningInstance F1 G1 1) : RawRU F1 C1 :=
  ⟨T.coords U.cmE, U.u, T.coords U.cmW, U.x⟩

def Setup.rawOfI (u : IncomingInstance G1 F1 1) : RawIU F1 C1 := ⟨T.coords u.cmW, u.x⟩

/-- Primary fold, verifier side, on proper objects. -/
def Setup.fold1 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1) :
    RunningInstance F1 G1 1 :=
  foldInstance (T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) π U u

end IVC
end Sonobe
