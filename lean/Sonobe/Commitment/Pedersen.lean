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

/-- A nontrivial discrete-log relation among the generators. Binding is exactly its absence. -/
def DLRel : Prop :=
  ∃ (c : Fin n → F) (s : F), (c ≠ 0 ∨ s ≠ 0) ∧ ∑ i, c i • ck.g i + s • ck.h = 0

end PedersenKey

section Binding

variable {F G : Type*} [Ring F] [AddCommGroup G] [Module F G] {n : ℕ}

/-- Binding reduces to the discrete-log relation: two distinct openings of one commitment
yield a nontrivial relation among the generators. -/
theorem PedersenKey.binding (ck : PedersenKey F G n) (hno : ¬ ck.DLRel)
    {v v' : Fin n → F} {r r' : F} (h : ck.commit v r = ck.commit v' r') :
    v = v' ∧ r = r' := by
  by_contra hne
  apply hno
  refine ⟨v - v', r - r', ?_, ?_⟩
  · by_contra hc
    simp only [not_or, not_not] at hc
    exact hne ⟨sub_eq_zero.mp hc.1, sub_eq_zero.mp hc.2⟩
  · have := sub_eq_zero.mpr h
    simpa [PedersenKey.commit, sub_smul, Finset.sum_sub_distrib, sub_add_sub_comm] using this

end Binding

/-- Smoke test over `ZMod 7`: `1·1 + 2·2 + 3·3 = 14 = 0`. -/
example : (PedersenKey.mk (F := ZMod 7) (G := ZMod 7) ![1, 2] 3).commit ![1, 2] 3 = 0 := by decide

end Sonobe
