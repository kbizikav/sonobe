import Sonobe.Circuit.FS2
import Sonobe.Circuit.Hash
import Sonobe.Circuit.Emulated.Absorb

/-!
The augmented circuit `AugmentedCircuit::compute_next_state`
(ivc/src/compilers/cyclefold/circuits.rs:93-203), one constraint group per Rust statement.

All wires are collected in `AugVars`. The relation `AugRel` is a *consequence* of the circuit's
constraints (the secondary challenges are only required to be boolean; their derivation from the
transcript is not needed for soundness), so only the direction `R1CS satisfied ⇒ AugRel` is trusted.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC2 Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModA {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

/-- Witnesses of one `to_affine` call. -/
structure AffWit (F : Type*) where
  x : F
  y : F
  inf : F
  zinv : F
  inv : F

def AffRel {F : Type*} [Field F] (P : PP F) (w : AffWit F) : Prop :=
  ToAffineRel P w.x w.y w.inf w.zinv w.inv

/-- Flatten absorbed pairs. -/
def prs {α : Type*} {n : ℕ} (a : Fin n → α × α) : List α := (List.ofFn a).flatMap pr

/-- All wires of the augmented circuit (`F = ZMod p1`, state of size `sN`). -/
structure AugVars (p1 sN : ℕ) where
  pp : ZMod p1
  i : ZMod p1
  invI : ZMod p1
  bc : ZMod p1
  z0 : Fin sN → ZMod p1
  zi : Fin sN → ZMod p1
  nx : Fin sN → ZMod p1
  Uu : ZMod p1
  Ux : ZMod p1
  uxIn : ZMod p1
  /-- emulated coordinates: `0 UE.x, 1 UE.y, 2 UW.x, 3 UW.y, 4 π.x, 5 π.y, 6 In.x, 7 In.y,
  8 pe.x, 9 pe.y, 10 pw.x, 11 pw.y` -/
  pa : Fin 12 → ℕ → ZMod p1
  pw : Fin 12 → TightWit p1 8 32
  /-- secondary running instance: `u, x₀..x₆` -/
  sa : Fin 8 → ℕ → ZMod p1
  sw : Fin 8 → TightWit p1 8 32
  sE : PP (ZMod p1)
  sW : PP (ZMod p1)
  c0W : PP (ZMod p1)
  c1W : PP (ZMod p1)
  cp0 : PP (ZMod p1)
  cp1 : PP (ZMod p1)
  rb0 : ℕ → ZMod p1
  rb1 : ℕ → ZMod p1
  o1a : Fin 8 → ℕ → ZMod p1
  o1E : PP (ZMod p1)
  o1W : PP (ZMod p1)
  o2a : Fin 8 → ℕ → ZMod p1
  o2E : PP (ZMod p1)
  o2W : PP (ZMod p1)
  -- the primary challenge
  c : ZMod p1
  cb : Fin 254 → ZMod p1
  -- absorption wires
  awU : Fin 4 → AbsWit p1
  aoU : Fin 4 → ZMod p1 × ZMod p1
  awS : Fin 8 → AbsWit p1
  aoS : Fin 8 → ZMod p1 × ZMod p1
  noU : Fin 2 → AffWit (ZMod p1)
  awT : Fin 8 → AbsWit p1
  aoT : Fin 8 → ZMod p1 × ZMod p1
  awN : Fin 4 → AbsWit p1
  aoN : Fin 4 → ZMod p1 × ZMod p1
  awM : Fin 8 → AbsWit p1
  aoM : Fin 8 → ZMod p1 × ZMod p1
  noM : Fin 2 → AffWit (ZMod p1)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- `c ? 0 : v`, the `select` against a zero dummy. -/
def selF0 (c v : ZMod p1) : ZMod p1 := c * (0 - v) + v

/-- Limb-wise select against a zero dummy. -/
def selLimbs (c : ZMod p1) (a : ℕ → ZMod p1) : ℕ → ZMod p1 := fun j => selF0 c (a j)

/-- Bits of the transcript challenge as a function on `ℕ`. -/
def cbN {p1 : ℕ} (cb : Fin 254 → ZMod p1) : ℕ → ZMod p1 := fun j => if h : j < 254 then cb ⟨j, h⟩ else 0

def secOf {F : Type*} (a : Fin 8 → ℕ → F) (E W : PP F) : SecVar F := ⟨a 0, fun j => a j.succ, E, W⟩

/-- The primary challenge as a field element. -/
def rhoOf {p1 : ℕ} (cb : Fin 254 → ZMod p1) : ZMod p1 := ∑ j ∈ range 128, cbN cb j * 2 ^ j

/-- The CycleFold incoming instances `cf_u` built by `to_cyclefold_inputs`
(adapters/nova.rs:94-126): public inputs `(ρ, P₀, P₁, P₂)` as emulated variables. -/
def cfI0 (v : AugVars p1 sN) : SecInc (ZMod p1) :=
  ⟨![rhoLimbs (cbN v.cb), v.pa 0, v.pa 1, v.pa 4, v.pa 5, v.pa 8, v.pa 9], v.c0W⟩

def cfI1 (v : AugVars p1 sN) : SecInc (ZMod p1) :=
  ⟨![rhoLimbs (cbN v.cb), v.pa 2, v.pa 3, v.pa 6, v.pa 7, v.pa 10, v.pa 11], v.c1W⟩

variable (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (EA : EmuArith p1 p2) (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G : ZMod p1 × ZMod p1) (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)

/-- Constraints of the augmented circuit; `uux` is its public output. -/
def AugRel (v : AugVars p1 sN) (uux : ZMod p1) : Prop :=
  -- 1. base case
  IsZeroRel v.i v.bc v.invI ∧ (∀ k, CondEqRel v.bc (v.z0 k) (v.zi k)) ∧
  -- allocations of the emulated coordinates and of the secondary running instance
  (∀ k, TightRel 8 32 (mlimb p2) (v.pa k) (v.pw k)) ∧
  (∀ k, TightRel 8 32 (mlimb p2) (v.sa k) (v.sw k)) ∧
  ValidPP W2 v.sE ∧ ValidPP W2 v.sW ∧
  -- 1.a  u_x = H(i, z₀, zᵢ, U, cf_U)
  (∀ k : Fin 4, EmuAbsRel (v.pa (Fin.castLE (by norm_num) k)) (v.awU k) (v.aoU k)) ∧
  (∀ k, EmuAbsRel (v.sa k) (v.awS k) (v.aoS k)) ∧
  AffRel v.sE (v.noU 0) ∧ AffRel v.sW (v.noU 1) ∧
  v.uxIn = hashOut sp (spInit sp v.pp dS)
    ([v.i] ++ List.ofFn v.z0 ++ List.ofFn v.zi ++ [v.Uu, v.Ux] ++ prs v.aoU ++ prs v.aoS ++
      pr ((v.noU 0).x, (v.noU 0).y) ++ pr ((v.noU 1).x, (v.noU 1).y)) ∧
  -- 1.c  ρ = challenge_bits(transcript.add(U).add(u).add(π))
  (∀ k : Fin 8, EmuAbsRel (v.pa (![0, 1, 2, 3, 6, 7, 4, 5] k)) (v.awT k) (v.aoT k)) ∧
  v.c = hashOut sp (spInit sp v.pp dT)
    ([v.Uu, v.Ux] ++ pr (v.aoT 0) ++ pr (v.aoT 1) ++ pr (v.aoT 2) ++ pr (v.aoT 3) ++ [v.uxIn] ++
      pr (v.aoT 4) ++ pr (v.aoT 5) ++ pr (v.aoT 6) ++ pr (v.aoT 7)) ∧
  ToBitsRel 254 pm1 v.c v.cb ∧
  -- 2. CycleFold side: the incoming instances have public inputs (ρ, P₀, P₁, P₂) and the
  --    secondary folds
  ValidPP W2 v.c0W ∧ ValidPP W2 v.c1W ∧ v.cp0.OnCurve W2.a₄ W2.a₆ ∧ v.cp1.OnCurve W2.a₄ W2.a₆ ∧
  FS2Rel W2 EA G (secOf v.sa v.sE v.sW) (cfI0 v) v.cp0 v.rb0 (secOf v.o1a v.o1E v.o1W) ∧
  FS2Rel W2 EA G (secOf v.o1a v.o1E v.o1W) (cfI1 v) v.cp1 v.rb1 (secOf v.o2a v.o2E v.o2W) ∧
  -- 3. next state
  StepRel v.zi v.nx ∧
  -- 4. uu_x = H(i+1, z₀, z_{i+1}, UU, cf_UU) with the dummies selected in the base case
  (∀ k : Fin 4, EmuAbsRel (selLimbs v.bc (v.pa (Fin.natAdd 8 k))) (v.awN k) (v.aoN k)) ∧
  (∀ k, EmuAbsRel (selLimbs v.bc (v.o2a k)) (v.awM k) (v.aoM k)) ∧
  AffRel (selPP v.bc zeroPP v.o2E) (v.noM 0) ∧ AffRel (selPP v.bc zeroPP v.o2W) (v.noM 1) ∧
  uux = hashOut sp (spInit sp v.pp dS)
    ([v.i + 1] ++ List.ofFn v.z0 ++ List.ofFn v.nx ++
      [selF0 v.bc (v.Uu + rhoOf v.cb), selF0 v.bc (v.uxIn * rhoOf v.cb + v.Ux)] ++
      prs v.aoN ++ prs v.aoM ++ pr ((v.noM 0).x, (v.noM 0).y) ++ pr ((v.noM 1).x, (v.noM 1).y))

end Gadget
end Sonobe
