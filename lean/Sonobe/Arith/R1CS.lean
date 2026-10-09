import Mathlib

/-!
R1CS / relaxed R1CS, modelled on `crates/primitives/src/arithmetizations/r1cs/mod.rs`.

Columns are `const-slot ⊕ public(l) ⊕ witness(nw)`; `evalR1CS z = Az ∘ Bz − z₀ • Cz`
(`evaluate_r1cs`, r1cs/mod.rs:104). Plain R1CS needs `z₀ = 1` and eval `= 0`;
relaxed R1CS with `z₀ = u` needs eval `= e` (r1cs/mod.rs:162, :199).
-/

namespace Sonobe

open Matrix

/-- Column index type. -/
abbrev Col (l nw : ℕ) := Unit ⊕ (Fin l ⊕ Fin nw)

structure R1CS (F : Type*) (m l nw : ℕ) where
  A : Matrix (Fin m) (Col l nw) F
  B : Matrix (Fin m) (Col l nw) F
  C : Matrix (Fin m) (Col l nw) F

namespace R1CS

variable {F : Type*} [CommRing F] {m l nw : ℕ}

/-- Assignment `z = (u, x, w)`. -/
def zvec (u : F) (x : Fin l → F) (w : Fin nw → F) : Col l nw → F :=
  Sum.elim (fun _ => u) (Sum.elim x w)

theorem zvec_add (u u' : F) (x x' : Fin l → F) (w w' : Fin nw → F) :
    zvec (u + u') (x + x') (w + w') = zvec u x w + zvec u' x' w' := by
  ext i; rcases i with _ | _ | _ <;> simp [zvec]

theorem zvec_smul (ρ u : F) (x : Fin l → F) (w : Fin nw → F) :
    zvec (ρ * u) (ρ • x) (ρ • w) = ρ • zvec u x w := by
  ext i; rcases i with _ | _ | _ <;> simp [zvec]

/-- `Az ∘ Bz − z₀ • Cz`. -/
def eval (r : R1CS F m l nw) (z : Col l nw → F) : Fin m → F :=
  (r.A *ᵥ z) * (r.B *ᵥ z) - z (Sum.inl ()) • (r.C *ᵥ z)

/-- Relaxed R1CS: `eval = e` with slack vector `e`. -/
def RelaxedSat (r : R1CS F m l nw) (u : F) (x : Fin l → F) (w : Fin nw → F) (e : Fin m → F) :
    Prop := r.eval (zvec u x w) = e

/-- Plain R1CS: `u = 1`, `e = 0`. -/
def Sat (r : R1CS F m l nw) (x : Fin l → F) (w : Fin nw → F) : Prop :=
  r.eval (zvec 1 x w) = 0

/-- The quadratic expansion that makes Nova folding work. -/
theorem eval_fold (r : R1CS F m l nw) (z₁ z₂ : Col l nw → F) (ρ : F) :
    r.eval (z₁ + ρ • z₂) =
      r.eval z₁ + ρ • (r.eval (z₁ + z₂) - r.eval z₁ - r.eval z₂) + (ρ ^ 2) • r.eval z₂ := by
  ext i
  simp [eval, mulVec_add, mulVec_smul]
  ring

end R1CS
end Sonobe
