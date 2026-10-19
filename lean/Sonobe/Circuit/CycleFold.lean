import Sonobe.Circuit.EC.ScalarMulSpec
import Sonobe.Circuit.Bits

/-!
The Nova CycleFold circuit `NovaCycleFoldCircuit::verify_point_rlc`
(ivc/src/compilers/cyclefold/adapters/nova.rs:55-64), **with the `EnforceValid` check** on the
witness points (primitives/src/algebra/group/mod.rs):

```
rho      = FpVar::new_input                       -- public 0
rho_bits = rho.to_n_bits_le(n)
points   = Vec::<C::Var>::new_witness             -- on-curve + enforce_valid, public 1..4 via to_affine
(points[1].scalar_mul_le(rho_bits) + points[0]).mark_as_public()   -- public 5..6
```
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

/-- All group-law lemmas are stated with the classical `DecidableEq`. -/
noncomputable local instance (priority := 10000) decEqZMod {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [Short W] [W.IsElliptic]

/-- Group element encoded by public affine coordinates; `(0, 0)` encodes the identity. -/
noncomputable def coordPt (xy : ZMod p × ZMod p) : W.toAffine.Point :=
  if xy = (0, 0) then 0 else ptOf W xy

/-- A projective witness as allocated by `ProjectiveVar::new_witness` followed by
`enforce_valid`: on the curve and not `(0, 0, 0)` (`NAND(y = 0, z = 0)`). -/
def ValidPP (P : PP (ZMod p)) : Prop :=
  P.OnCurve W.a₄ W.a₆ ∧ ¬ (P.y = 0 ∧ P.z = 0)

omit [Short W] [W.IsElliptic] in
theorem ValidPP.not_isZero {P : PP (ZMod p)} (h : ValidPP W P) : ¬ P.IsZero := fun hz => h.2 ⟨hz.2.1, hz.2.2⟩

/-- Witnesses of the CycleFold circuit. -/
structure CFWit (F : Type*) where
  bits : ℕ → F
  P₀ : PP F
  P₁ : PP F
  inf₀ : F
  zinv₀ : F
  inv₀ : F
  inf₁ : F
  zinv₁ : F
  inv₁ : F
  sm : SMWit F
  infR : F
  zinvR : F
  invR : F

/-- Public inputs `[ρ, P₀.x, P₀.y, P₁.x, P₁.y, R.x, R.y]`. -/
def CFRel (n : ℕ) (G : ZMod p × ZMod p) (ρ p0x p0y p1x p1y rx ry : ZMod p) (w : CFWit (ZMod p)) :
    Prop :=
  ToNBitsRel n ρ (fun i : Fin n => w.bits i) ∧
  ValidPP W w.P₀ ∧ ValidPP W w.P₁ ∧
  ToAffineRel w.P₀ p0x p0y w.inf₀ w.zinv₀ w.inv₀ ∧
  ToAffineRel w.P₁ p1x p1y w.inf₁ w.zinv₁ w.inv₁ ∧
  SMRel W n G w.bits w.P₁ w.sm ∧
  ToAffineRel (rcb W.a₄ W.a₆ (smOut W n G w.bits w.sm) w.P₀) rx ry w.infR w.zinvR w.invR

/-- Public coordinates of a valid projective point decode to its group element. -/
theorem coordPt_affine (hb : W.a₆ ≠ 0) {P : PP (ZMod p)} (hP : P.OnCurve W.a₄ W.a₆)
    {x y inf zinv inv : ZMod p} (h : ToAffineRel P x y inf zinv inv) :
    coordPt W (x, y) = P.pt W := by
  obtain ⟨hz0, hz1⟩ := toAffine_sound h
  by_cases hz : P.z = 0
  · obtain ⟨-, hx, hy⟩ := hz0 hz
    simp [coordPt, hx, hy, pt_of_z_zero W hz]
  · obtain ⟨-, hx, hy⟩ := hz1 hz
    have hE := equation_of_onCurve W hz hP
    have hE' : W.toAffine.Equation x y := by rw [hx, hy]; exact hE
    have hne : (x, y) ≠ (0, 0) := by
      intro h0
      simp only [Prod.mk.injEq] at h0
      have := (equation_short W).mp hE'
      rw [h0.1, h0.2] at this
      apply hb; simpa using this.symm
    rw [coordPt, if_neg hne, ptOf_eq W hE', pt_of_equation W hz hE]
    simp [hx, hy]

theorem natVal_bitsOf (n : ℕ) (w : ℕ → ZMod p) :
    natVal n (bitsOf (fun i : Fin n => w i)) = natVal n (fun j => decide (w j = 1)) := by
  unfold natVal
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  simp [bitsOf, this]

/-- **CycleFold soundness**: the public inputs satisfy `R = P₀ + ρ · P₁` in the group, with `ρ`
the integer encoded by the `n` boolean witnesses. -/
theorem cf_sound (hb : W.a₆ ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hnr : ∀ e : ZMod p, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) {n : ℕ} (hn : 1 ≤ n)
    (hrn : 2 ^ n < r) (hnp : 2 ^ n ≤ p) {G : ZMod p × ZMod p}
    {ρ p0x p0y p1x p1y rx ry : ZMod p} {w : CFWit (ZMod p)}
    (h : CFRel W n G ρ p0x p0y p1x p1y rx ry w) :
    ρ.val < 2 ^ n ∧
      coordPt W (rx, ry) = coordPt W (p0x, p0y) + ρ.val • coordPt W (p1x, p1y) := by
  obtain ⟨hρ, hv0, hv1, ha0, ha1, hsm, haR⟩ := h
  have hbool : ∀ i < n, IsBool (w.bits i) := fun i hi => hρ.1 ⟨i, hi⟩
  obtain ⟨hval, hlt⟩ := toNBits_sound hnp hρ
  rw [natVal_bitsOf] at hval
  obtain ⟨hS_c, hS_n, hS_p⟩ :=
    scalar_mul_sound W h2 hnr hord hn hrn hbool hv1.1 hsm
  obtain ⟨hR_c, hR_n, hR_p⟩ := rcb_spec W h2 hnr hS_c hv0.1 hS_n hv0.not_isZero
  refine ⟨hlt, ?_⟩
  rw [coordPt_affine W hb hR_c haR, coordPt_affine W hb hv0.1 ha0, coordPt_affine W hb hv1.1 ha1,
    hR_p, hS_p, hval, add_comm]

end Gadget
end Sonobe
