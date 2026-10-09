import Mathlib

/-!
Linear-subspace SNARK, modelled on `crates/snarks/src/linear_subspace/mod.rs`.

For a matrix `M : rows × cols → G₁` and a hidden `k : rows → F`, `a ∈ G₂`:
* `pk.p = Mᵀ k`                       (generate_keys: `mvm k`),
* `vk.c_j = k_j • a`, `vk.a_neg = -a`,
* `prove w = ⟨p, w⟩`,
* `verify x π ⇔ Σ_j e(x_j, k_j a) + e(π, -a) = 0`.
The pairing is an `F`-bilinear map `e`; the target group is written additively.
-/

namespace Sonobe
namespace LinearSubspace

variable {F G₁ G₂ G_T : Type*} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup G_T] [Module F G_T]
variable {R : Type*} [Fintype R] {ι : Type*} [Fintype ι]

/-- `ProverKey.p` (mod.rs:33). -/
def pk (M : R → ι → G₁) (k : R → F) : ι → G₁ := fun i => ∑ j, k j • M j i

/-- `prove` (mod.rs:47). -/
def prove (p : ι → G₁) (w : ι → F) : G₁ := ∑ i, w i • p i

/-- `verify` (mod.rs:50). -/
def Verify (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (a : G₂) (k : R → F) (x : R → G₁) (π : G₁) : Prop :=
  ∑ j, e (x j) (k j • a) + e π (-a) = 0

/-- **Completeness**: if `x = M w` the honest proof verifies. -/
theorem complete (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (a : G₂) (M : R → ι → G₁) (k : R → F)
    (w : ι → F) (x : R → G₁) (hx : ∀ j, x j = ∑ i, w i • M j i) :
    Verify e a k x (prove (pk M k) w) := by
  have hπ : prove (pk M k) w = ∑ j, k j • x j := by
    simp only [prove, pk, hx, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  simp only [Verify, hπ, map_smul, map_neg, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
  simp [Finset.sum_neg_distrib]

/-- The verification equation forces `π = Σ_j k_j x_j` when `e(·, a)` is injective. -/
theorem verify_eq (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (a : G₂) (hinj : Function.Injective fun g => e g a)
    {k : R → F} {x : R → G₁} {π : G₁} (h : Verify e a k x π) : π = ∑ j, k j • x j := by
  apply hinj
  have h' : ∑ j, k j • e (x j) a + (-e π a) = 0 := by simpa [Verify] using h
  show e π a = e (∑ j, k j • x j) a
  rw [map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply]
  exact (add_neg_eq_zero.mp h').symm

/-- Generic-group step of the soundness argument: if the relation `Σ_j k_j (x_j - (M w)_j) = 0`
holds identically in the hidden `k`, every row is satisfied. -/
theorem rows_of_identity [DecidableEq R] (M : R → ι → G₁) (x : R → G₁) (w : ι → F)
    (h : ∀ k : R → F, ∑ j, k j • (x j - ∑ i, w i • M j i) = 0) :
    ∀ j, x j = ∑ i, w i • M j i := by
  intro j
  have := h (Pi.single j 1)
  simpa [Pi.single_apply, sub_eq_zero] using this

end LinearSubspace
end Sonobe
