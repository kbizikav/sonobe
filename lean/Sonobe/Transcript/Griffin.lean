import Mathlib

/-!
Griffin permutation, modelled on `crates/primitives/src/transcripts/griffin/mod.rs`
(`Griffin::non_linear` :348, `Griffin::permute` :386, `GriffinGadget::non_linear` :415).

Parameters are abstract: `GriffinParams::new` derives them from SHAKE128 (not formalised).
`root` is the `x ↦ x^(d⁻¹)` map (`d_inv` square-and-multiply); the circuit instead allocates a
witness `y₀` and enforces `y₀^d = x₀` (mod.rs:442). `hinj` (`gcd(d, p-1) = 1`) makes that sound.
-/

namespace Sonobe

structure GriffinParams (F : Type*) [Field F] where
  t : ℕ
  ht : 2 ≤ t
  d : ℕ
  rounds : ℕ
  root : F → F
  hroot : ∀ x, root x ^ d = x
  hinj : ∀ x y : F, x ^ d = y ^ d → x = y
  alpha : ℕ → F
  beta : ℕ → F
  mat : Matrix (Fin t) (Fin t) F
  rc : ℕ → Fin t → F

namespace GriffinParams

variable {F : Type*} [Field F] (p : GriffinParams F)

/-- Total read, `0` out of range. -/
def rd (x : Fin p.t → F) (k : ℕ) : F := if h : k < p.t then x ⟨k, h⟩ else 0

/-- `l_i = y₁ + (i-1)·y₀ (+ x_{i-1} if i > 2)`, given the outputs `y₀ y₁` (mod.rs:373-380). -/
def lin (x : Fin p.t → F) (y₀ y₁ : F) (i : ℕ) : F :=
  y₁ + ((i - 1 : ℕ) : F) * y₀ + (if 2 < i then p.rd x (i - 1) else 0)

/-- Output `i` of the non-linear layer for `i ≥ 2`. -/
def tail (x : Fin p.t → F) (y₀ y₁ : F) (i : ℕ) : F :=
  p.rd x i * (p.lin x y₀ y₁ i ^ 2 + p.alpha (i - 2) * p.lin x y₀ y₁ i + p.beta (i - 2))

/-- `Griffin::non_linear` (mod.rs:348). -/
def nonlinear (x : Fin p.t → F) : Fin p.t → F := fun i =>
  if i.val = 0 then p.root (p.rd x 0)
  else if i.val = 1 then p.rd x 1 ^ p.d
  else p.tail x (p.root (p.rd x 0)) (p.rd x 1 ^ p.d) i.val

/-- `Griffin::affine` (mod.rs:~300): matrix, plus round constant unless in the last round. -/
def affine (r : ℕ) (s : Fin p.t → F) : Fin p.t → F :=
  p.mat.mulVec s + if r + 1 < p.rounds then p.rc r else 0

/-- State after the initial affine layer and `r` rounds. -/
def iter (s : Fin p.t → F) : ℕ → (Fin p.t → F)
  | 0 => p.affine p.rounds s
  | r + 1 => p.affine r (p.nonlinear (iter s r))

/-- `Griffin::permute` (mod.rs:386). -/
def permute (s : Fin p.t → F) : Fin p.t → F := p.iter s p.rounds

/-! ### Constraint system (`GriffinGadget`) -/

/-- Constraints of one non-linear layer; `y 0` is the free witness. -/
def NLRel (x y : Fin p.t → F) : Prop :=
  (∀ i : Fin p.t, i.val = 0 → y i ^ p.d = p.rd x 0) ∧
  (∀ i : Fin p.t, i.val = 1 → y i = p.rd x 1 ^ p.d) ∧
  (∀ i : Fin p.t, 2 ≤ i.val → y i = p.tail x (p.rd y 0) (p.rd y 1) i.val)

theorem rd_apply (x : Fin p.t → F) (i : Fin p.t) : p.rd x i.val = x i := by
  simp [rd, i.isLt]

theorem rd_nonlinear_zero (x : Fin p.t → F) : p.rd (p.nonlinear x) 0 = p.root (p.rd x 0) := by
  have := p.rd_apply (p.nonlinear x) ⟨0, by have := p.ht; omega⟩
  simp only at this
  rw [this]; simp [nonlinear]

theorem rd_nonlinear_one (x : Fin p.t → F) : p.rd (p.nonlinear x) 1 = p.rd x 1 ^ p.d := by
  have := p.rd_apply (p.nonlinear x) ⟨1, by have := p.ht; omega⟩
  simp only at this
  rw [this]; simp [nonlinear]

/-- The non-linear constraints pin the output down: soundness and completeness. -/
theorem nlRel_iff (x y : Fin p.t → F) : p.NLRel x y ↔ y = p.nonlinear x := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h0t : 0 < p.t := by have := p.ht; omega
    have h1t : 1 < p.t := by have := p.ht; omega
    have e0 : p.rd y 0 = p.root (p.rd x 0) := by
      rw [show p.rd y 0 = y ⟨0, h0t⟩ from p.rd_apply y ⟨0, h0t⟩]
      exact p.hinj _ _ (by rw [h0 ⟨0, h0t⟩ rfl, p.hroot])
    have e1 : p.rd y 1 = p.rd x 1 ^ p.d := by
      rw [show p.rd y 1 = y ⟨1, h1t⟩ from p.rd_apply y ⟨1, h1t⟩]
      exact h1 ⟨1, h1t⟩ rfl
    funext i
    by_cases hi0 : i.val = 0
    · have := p.rd_apply y i
      rw [hi0] at this
      rw [← this, e0]; simp [nonlinear, hi0]
    by_cases hi1 : i.val = 1
    · have := p.rd_apply y i
      rw [hi1] at this
      rw [← this, e1]; simp [nonlinear, hi1]
    · rw [h2 i (by omega), e0, e1]; simp [nonlinear, hi0, hi1]
  · rintro rfl
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · simp [nonlinear, hi, p.hroot]
    · simp [nonlinear, hi]
    · rw [rd_nonlinear_zero, rd_nonlinear_one]
      have : i.val ≠ 0 := by omega
      have : i.val ≠ 1 := by omega
      simp [nonlinear, *]

/-- Circuit-side state chain: `ys r` is the witnessed non-linear output of round `r`. -/
def cur (inp : Fin p.t → F) (ys : ℕ → Fin p.t → F) : ℕ → (Fin p.t → F)
  | 0 => p.affine p.rounds inp
  | r + 1 => p.affine r (ys r)

/-- Permutation circuit: one witness layer per round, chained through the affine maps. -/
def PermRel (inp out : Fin p.t → F) : Prop :=
  ∃ ys : ℕ → Fin p.t → F, (∀ r < p.rounds, p.NLRel (p.cur inp ys r) (ys r)) ∧
    out = p.cur inp ys p.rounds

/-- **Bind**: the permutation circuit is satisfiable exactly at `permute inp`
(no under-constrained output, no unsatisfiable honest run). -/
theorem permRel_iff (inp out : Fin p.t → F) : p.PermRel inp out ↔ out = p.permute inp := by
  constructor
  · rintro ⟨ys, hys, rfl⟩
    have key : ∀ r ≤ p.rounds, p.cur inp ys r = p.iter inp r := by
      intro r
      induction r with
      | zero => intro _; rfl
      | succ r ih =>
        intro hr
        have h := (p.nlRel_iff _ _).mp (hys r (by omega))
        rw [show p.cur inp ys (r + 1) = p.affine r (ys r) from rfl,
          show p.iter inp (r + 1) = p.affine r (p.nonlinear (p.iter inp r)) from rfl, h, ih (by omega)]
    exact key _ le_rfl
  · rintro rfl
    refine ⟨fun r => p.nonlinear (p.iter inp r), fun r _ => ?_, ?_⟩
    · rw [nlRel_iff]
      have key : ∀ r, p.cur inp (fun r => p.nonlinear (p.iter inp r)) r = p.iter inp r := by
        intro r
        cases r <;> rfl
      rw [key]
    · cases h : p.rounds with
      | zero => simp [permute, iter, cur, h]
      | succ n => simp [permute, iter, cur, h]

end GriffinParams
end Sonobe
