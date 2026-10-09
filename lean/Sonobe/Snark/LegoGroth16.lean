import Sonobe.Snark.LinearSubspace

/-!
LegoGroth16 (commit-and-prove Groth16), modelled on `crates/snarks/src/cp/legogroth16/mod.rs`
(`prove` :400, `verify` :514).

Group elements are written as multiples of the generators `g₁`, `g₂` (so the setup scalars
`α β γ δ η` and the QAP evaluations live in `F`). The checks are

* Groth16:  `e(A,B) · e(D + g_ic, -γ) · e(C, -δ) = e(α, β)`,
* link:     `Σ_j e(c_j, k_j a) + e(D, k_m a) + e(π, -a) = 0`.
-/

namespace Sonobe
namespace LegoGroth16

variable {F : Type*} [Field F]

/-- The scalar identity behind Groth16 completeness. `SA SB SC` are the QAP sums at `t`, and
`KP KK KW` the sums of `kⱼ wⱼ = (β aⱼ + α bⱼ + cⱼ) wⱼ` over public / committed / other witnesses. -/
theorem groth16_scalar {α β γ δ η r s v hq SA SB SC KP KK KW : F} (hγ : γ ≠ 0) (hδ : δ ≠ 0)
    (hk : KP + KK + KW = β * SA + α * SB + SC) (hqap : SA * SB = SC + δ * hq) :
    (α + SA + r * δ) * (β + SB + s * δ) =
      ((KK / γ + v * η / γ) + KP / γ) * γ +
      (s * (α + SA + r * δ) + r * (β + SB + s * δ) - r * s * δ + KW / δ + hq - v * η / δ) * δ
        + α * β := by
  field_simp
  linear_combination hqap - hk

/-! ### Full completeness (Groth16 check and link check) -/

section Complete

variable {G₁ G₂ G_T : Type*} [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup G_T] [Module F G_T]
variable {P K W C : Type*} [Fintype P] [Fintype K] [Fintype W] [Fintype C] [DecidableEq C]

/-- Setup scalars and QAP evaluations at the secret point `t` (setup, mod.rs:161-398). -/
structure Params (F : Type*) (P K W : Type*) where
  α : F
  β : F
  γ : F
  δ : F
  η : F
  qa : P ⊕ K ⊕ W → F
  qb : P ⊕ K ⊕ W → F
  qc : P ⊕ K ⊕ W → F

/-- `k_j = β a_j + α b_j + c_j`. -/
def Params.kk (pp : Params F P K W) (i : P ⊕ K ⊕ W) : F := pp.β * pp.qa i + pp.α * pp.qb i + pp.qc i

variable (pp : Params F P K W)

/-- Satisfying assignment `(x, w_committed, w_other)` of the QAP at `t`, with `hq` the scaled
`h(t) Z(t) / δ` contribution. -/
def Qap (x : P → F) (wc : K → F) (ww : W → F) (hq : F) : Prop :=
  (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) * (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) =
    (∑ i, pp.qc i * Sum.elim x (Sum.elim wc ww) i) + pp.δ * hq

theorem k_split (x : P → F) (wc : K → F) (ww : W → F) :
    (∑ p, pp.kk (Sum.inl p) * x p) + (∑ k, pp.kk (Sum.inr (Sum.inl k)) * wc k) +
        (∑ w, pp.kk (Sum.inr (Sum.inr w)) * ww w) =
      pp.β * (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) +
        pp.α * (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) +
        (∑ i, pp.qc i * Sum.elim x (Sum.elim wc ww) i) := by
  set z : P ⊕ K ⊕ W → F := Sum.elim x (Sum.elim wc ww) with hz
  have h1 : ∀ i, pp.kk i * z i = pp.β * (pp.qa i * z i) + pp.α * (pp.qb i * z i) + pp.qc i * z i := by
    intro i; simp only [Params.kk]; ring
  calc (∑ p, pp.kk (Sum.inl p) * x p) + (∑ k, pp.kk (Sum.inr (Sum.inl k)) * wc k) +
        (∑ w, pp.kk (Sum.inr (Sum.inr w)) * ww w) = ∑ i, pp.kk i * z i := by
        simp [Fintype.sum_sum_type, hz, add_assoc]
    _ = ∑ i, (pp.β * (pp.qa i * z i) + pp.α * (pp.qb i * z i) + pp.qc i * z i) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]

variable (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (g₁ : G₁) (g₂ : G₂)

theorem pair_smul (x y : F) : e (x • g₁) (y • g₂) = (x * y) • e g₁ g₂ := by
  simp [map_smul, smul_smul, mul_comm]

/-- The Groth16 pairing check of `verify` (mod.rs:525). -/
def Groth16Check (A : G₁) (B : G₂) (Cc D gic : G₁) : Prop :=
  e A B + e (D + gic) (-(pp.γ • g₂)) + e Cc (-(pp.δ • g₂)) = e (pp.α • g₁) (pp.β • g₂)

/-- **Groth16 completeness** in the group: the honest `(A, B, C, D)` (prove, mod.rs:433-491) pass the
pairing check whenever the QAP holds at `t`. -/
theorem groth16_complete (hγ : pp.γ ≠ 0) (hδ : pp.δ ≠ 0) (x : P → F) (wc : K → F) (ww : W → F)
    (hq r s v : F) (hqap : Qap pp x wc ww hq) :
    Groth16Check pp e g₁ g₂
      ((pp.α + (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) + r * pp.δ) • g₁)
      ((pp.β + (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) + s * pp.δ) • g₂)
      ((s * (pp.α + (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) + r * pp.δ)
        + r * (pp.β + (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) + s * pp.δ)
        - r * s * pp.δ + (∑ w, pp.kk (Sum.inr (Sum.inr w)) * ww w) / pp.δ + hq
        - v * pp.η / pp.δ) • g₁)
      (((∑ k, pp.kk (Sum.inr (Sum.inl k)) * wc k) / pp.γ + v * pp.η / pp.γ) • g₁)
      (((∑ p, pp.kk (Sum.inl p) * x p) / pp.γ) • g₁) := by
  have sc := groth16_scalar (r := r) (s := s) (v := v) (η := pp.η) hγ hδ (k_split pp x wc ww) hqap
  have key : ∀ a b : F, e (a • g₁) (-(b • g₂)) = -((a * b) • e g₁ g₂) := by
    intro a b; rw [map_neg, pair_smul]
  unfold Groth16Check
  rw [← add_smul, pair_smul, key, key, pair_smul]
  rw [sc, add_smul, add_smul]
  abel

/-! #### The link matrix (mod.rs:324-346) -/

variable (blk : K → C) (gK : K → G₁) (hC : C → G₁)

/-- Rows: one per Pedersen commitment `j`, then the row of `D`. Columns: committed values,
commitment randomness `o`, and the Groth16 blinder `v`. -/
def linkM : C ⊕ Unit → K ⊕ C ⊕ Unit → G₁
  | .inl j, .inl i => if blk i = j then gK i else 0
  | .inl j, .inr (.inl j') => if j' = j then hC j else 0
  | .inl _, .inr (.inr _) => 0
  | .inr _, .inl i => (pp.kk (Sum.inr (Sum.inl i)) / pp.γ) • g₁
  | .inr _, .inr (.inl _) => 0
  | .inr _, .inr (.inr _) => (pp.η / pp.γ) • g₁

def omega (wc : K → F) (o : C → F) (v : F) : K ⊕ C ⊕ Unit → F :=
  Sum.elim wc (Sum.elim o (fun _ => v))

/-- Pedersen commitment `j` to its block of committed variables. -/
def cm (wc : K → F) (o : C → F) (j : C) : G₁ :=
  (∑ i, if blk i = j then wc i • gK i else 0) + o j • hC j

/-- `D` (mod.rs:489). -/
def dElt (wc : K → F) (v : F) : G₁ :=
  (((∑ k, pp.kk (Sum.inr (Sum.inl k)) * wc k) / pp.γ + v * pp.η / pp.γ) • g₁)

theorem row_cm (wc : K → F) (o : C → F) (v : F) (j : C) :
    ∑ i, omega wc o v i • linkM pp g₁ blk gK hC (.inl j) i = cm blk gK hC wc o j := by
  simp [Fintype.sum_sum_type, omega, linkM, cm, apply_ite]

theorem row_d (wc : K → F) (o : C → F) (v : F) :
    ∑ i, omega wc o v i • linkM pp g₁ blk gK hC (.inr ()) i = dElt pp g₁ wc v := by
  simp only [Fintype.sum_sum_type, omega, linkM, dElt, Sum.elim_inl, Sum.elim_inr, smul_smul,
    smul_zero, Finset.sum_const_zero, add_zero]
  simp [← Finset.sum_smul, ← add_smul, add_div, Finset.sum_div, mul_div_assoc, mul_comm]

variable (ak : G₂) (kl : C ⊕ Unit → F)

/-- **LegoGroth16 completeness** (verify, mod.rs:514-547): both the Groth16 check and the link
check accept the honest proof, for the commitments `c_j = cm j`. -/
theorem lego_complete (hγ : pp.γ ≠ 0) (hδ : pp.δ ≠ 0) (x : P → F) (wc : K → F) (ww : W → F)
    (hq r s v : F) (o : C → F) (hqap : Qap pp x wc ww hq) :
    Groth16Check pp e g₁ g₂
      ((pp.α + (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) + r * pp.δ) • g₁)
      ((pp.β + (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) + s * pp.δ) • g₂)
      ((s * (pp.α + (∑ i, pp.qa i * Sum.elim x (Sum.elim wc ww) i) + r * pp.δ)
        + r * (pp.β + (∑ i, pp.qb i * Sum.elim x (Sum.elim wc ww) i) + s * pp.δ)
        - r * s * pp.δ + (∑ w, pp.kk (Sum.inr (Sum.inr w)) * ww w) / pp.δ + hq
        - v * pp.η / pp.δ) • g₁)
      (dElt pp g₁ wc v) (((∑ p, pp.kk (Sum.inl p) * x p) / pp.γ) • g₁) ∧
    LinearSubspace.Verify e ak kl
      (Sum.elim (cm blk gK hC wc o) (fun _ => dElt pp g₁ wc v))
      (LinearSubspace.prove (LinearSubspace.pk (linkM pp g₁ blk gK hC) kl) (omega wc o v)) := by
  refine ⟨groth16_complete pp e g₁ g₂ hγ hδ x wc ww hq r s v hqap, ?_⟩
  refine LinearSubspace.complete e ak _ kl (omega wc o v) _ ?_
  rintro (j | ⟨⟩)
  · exact (row_cm pp g₁ blk gK hC wc o v j).symm
  · exact (row_d pp g₁ blk gK hC wc o v).symm

end Complete



end LegoGroth16
end Sonobe
