import Sonobe.Nova.Soundness
import Sonobe.IVC.Model

/-!
Coordinate-level model of the Nova + CycleFold IVC.

Unlike `Sonobe.IVC.Model`, the primary commitments handled by the augmented circuit are *raw
coordinate pairs* (`C1`): the circuit allocates them as `EmulatedAffineVar`s with a range check but no
curve check. That they are genuine group elements follows only from the CycleFold circuit, which
allocates them as curve points; this is made explicit in `CFSound2`.

The hash also takes the public-parameter hash `pph` as an argument: in the augmented circuit it is
a free witness (`FpVar::new_witness(pp_hash)`), so the verifier's hash binds it.
-/

namespace Sonobe
namespace IVC2

open Nova IVC

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2]

/-- A primary running instance whose commitments are raw coordinates. -/
structure RawRU (F C : Type*) where
  cmE : C
  u : F
  cmW : C
  x : Fin 1 → F

structure RawIU (F C : Type*) where
  cmW : C
  x : Fin 1 → F

structure Setup2 (F1 G1 F2 G2 S C1 : Type*) [Field F1] [AddCommGroup G1] [Module F1 G1]
    [Field F2] [AddCommGroup G2] [Module F2 G2] where
  m1 : ℕ
  nw1 : ℕ
  m2 : ℕ
  l2 : ℕ
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

variable (T : Setup2 F1 G1 F2 G2 S C1)

/-- The primary challenge as a field element. -/
def Setup2.ch1 (pp : F1) (U : RawRU F1 C1) (u : RawIU F1 C1) (π : C1) : F1 := (T.ch1n pp U u π : F1)

def Setup2.rawOf (U : RunningInstance F1 G1 1) : RawRU F1 C1 :=
  ⟨T.coords U.cmE, U.u, T.coords U.cmW, U.x⟩

def Setup2.rawOfI (u : IncomingInstance G1 F1 1) : RawIU F1 C1 := ⟨T.coords u.cmW, u.x⟩

/-- Primary fold, verifier side, on proper objects. -/
def Setup2.fold1 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1) :
    RunningInstance F1 G1 1 :=
  foldInstance (T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) π U u

end IVC2
end Sonobe
