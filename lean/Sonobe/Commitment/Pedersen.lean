import Mathlib

/-!
Pedersen commitment, modelled on `crates/primitives/src/commitments/pedersen.rs`.

`cm = ⟨g, v⟩ + r • h` (hiding, `PedersenKey::new` with `H = true`); the non-hiding
variant is the same with `h = 0`. Open is recompute-and-compare (pedersen.rs:211, :232).
-/

namespace Sonobe

variable {F G : Type*} [Semiring F] [AddCommMonoid G] [Module F G]

/-- `PedersenKey { g, h }` (pedersen.rs:41). -/
structure PedersenKey (F G : Type*) [Semiring F] [AddCommMonoid G] [Module F G] (n : ℕ) where
  g : Fin n → G
  h : G

namespace PedersenKey

variable {n : ℕ} (ck : PedersenKey F G n)

/-- `commit` (pedersen.rs:69). -/
def commit (v : Fin n → F) (r : F) : G := ∑ i, v i • ck.g i + r • ck.h

/-- `open`: recompute and compare. -/
def Opens (v : Fin n → F) (r : F) (cm : G) : Prop := ck.commit v r = cm

theorem opens_commit (v r) : ck.Opens v r (ck.commit v r) := rfl

theorem commit_zero : ck.commit 0 0 = 0 := by simp [commit]

theorem commit_add (v v' : Fin n → F) (r r' : F) :
    ck.commit (v + v') (r + r') = ck.commit v r + ck.commit v' r' := by
  simp [commit, add_smul, Finset.sum_add_distrib]
  abel

theorem commit_smul {F G : Type*} [CommSemiring F] [AddCommMonoid G] [Module F G]
    (ck : PedersenKey F G n) (a : F) (v : Fin n → F) (r : F) :
    ck.commit (a • v) (a * r) = a • ck.commit v r := by
  simp [commit, smul_add, Finset.smul_sum, mul_smul]

/-- Folding step: `commit (v + ρ v') (r + ρ r') = commit v r + ρ • commit v' r'`. -/
theorem commit_fold {F G : Type*} [CommRing F] [AddCommMonoid G] [Module F G]
    (ck : PedersenKey F G n) (ρ : F) (v v' : Fin n → F) (r r' : F) :
    ck.commit (v + ρ • v') (r + ρ * r') = ck.commit v r + ρ • ck.commit v' r' := by
  rw [commit_add, commit_smul]

/-- **Binding at two openings**: `(v, r)` and `(v', r')` are not two different openings of one
commitment. -/
def BindsAt (v : Fin n → F) (r : F) (v' : Fin n → F) (r' : F) : Prop :=
  ck.commit v r = ck.commit v' r' → v = v' ∧ r = r'

theorem bindsAt_self (v : Fin n → F) (r : F) : ck.BindsAt v r v r := fun _ => ⟨rfl, rfl⟩

end PedersenKey

section Binding

variable {F G : Type*} [Ring F] [AddCommGroup G] [Module F G] {n : ℕ}

/-- **The reduction**: two different openings of one commitment are a discrete-log relation
among the generators, with coefficients `v - v'`, `r - r'` computed from them. -/
theorem PedersenKey.dlRel_of_not_bindsAt (ck : PedersenKey F G n) {v v' : Fin n → F} {r r' : F}
    (h : ¬ ck.BindsAt v r v' r') :
    (v - v' ≠ 0 ∨ r - r' ≠ 0) ∧ ∑ i, (v - v') i • ck.g i + (r - r') • ck.h = 0 := by
  simp only [PedersenKey.BindsAt, Classical.not_imp] at h
  obtain ⟨hc, hne⟩ := h
  refine ⟨?_, ?_⟩
  · by_contra hz
    simp only [not_or, not_not, sub_eq_zero] at hz
    exact hne hz
  · have := sub_eq_zero.mpr hc
    simpa [PedersenKey.commit, sub_smul, Finset.sum_sub_distrib, sub_add_sub_comm] using this

end Binding

/-- Smoke test over `ZMod 7`: `1·1 + 2·2 + 3·3 = 14 = 0`. -/
example : (PedersenKey.mk (F := ZMod 7) (G := ZMod 7) ![1, 2] 3).commit ![1, 2] 3 = 0 := by decide

end Sonobe
