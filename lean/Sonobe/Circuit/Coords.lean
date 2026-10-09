import Sonobe.Circuit.CycleFold

/-!
Group elements ↔ affine coordinates (identity ↦ `(0, 0)`), as used by `to_affine`, `Inputize`
and the absorb gadgets.
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [Short W] [W.IsElliptic]

noncomputable local instance decEqZMod' {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

/-- Affine coordinates of a point; the identity is `(0, 0)`. -/
noncomputable def coordsOf : W.toAffine.Point → ZMod p × ZMod p
  | .zero => (0, 0)
  | .some x y _ => (x, y)

theorem coordsOf_injective (hb : W.a₆ ≠ 0) : Function.Injective (coordsOf W) := by
  have hne : ∀ {x y : ZMod p}, W.toAffine.Equation x y → (x, y) ≠ (0, 0) := by
    intro x y hE h0
    simp only [Prod.mk.injEq] at h0
    have := (equation_short W).mp hE
    rw [h0.1, h0.2] at this
    apply hb; simpa using this.symm
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ =>
      exfalso
      exact hne ((equation_iff_nonsingular).mpr hQ) (by simpa [coordsOf] using h.symm)
  | some x y hP =>
    cases Q with
    | zero =>
      exfalso
      exact hne ((equation_iff_nonsingular).mpr hP) (by simpa [coordsOf] using h)
    | some x' y' hQ =>
      simp only [coordsOf, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl

/-- The point encoded by public coordinates is the point we started from. -/
theorem coordPt_coordsOf (hb : W.a₆ ≠ 0) (P : W.toAffine.Point) : coordPt W (coordsOf W P) = P := by
  cases P with
  | zero => simp [coordsOf, coordPt]; rfl
  | some x y h =>
    have hE : W.toAffine.Equation x y := (equation_iff_nonsingular (W := W.toAffine)).mpr h
    have hne : ((x, y) : ZMod p × ZMod p) ≠ (0, 0) := by
      intro h0
      simp only [Prod.mk.injEq] at h0
      have := (equation_short W).mp hE
      rw [h0.1, h0.2] at this
      apply hb; simpa using this.symm
    simp only [coordsOf, coordPt, if_neg hne]
    rw [ptOf_eq W (xy := (x, y)) hE]
    rfl

/-- A valid projective point's public affine coordinates are the coordinates of its group element. -/
theorem coordsOf_pt_affine {P : PP (ZMod p)} (hP : P.OnCurve W.a₄ W.a₆) {x y inf zinv inv : ZMod p}
    (h : ToAffineRel P x y inf zinv inv) : coordsOf W (P.pt W) = (x, y) := by
  obtain ⟨hz0, hz1⟩ := toAffine_sound h
  by_cases hz : P.z = 0
  · obtain ⟨-, hx, hy⟩ := hz0 hz
    simp [pt_of_z_zero W hz, coordsOf, hx, hy]
  · obtain ⟨-, hx, hy⟩ := hz1 hz
    have hE := equation_of_onCurve W hz hP
    rw [pt_of_equation W hz hE]
    simp [Affine.Point.mk, coordsOf, hx, hy]

/-- **CycleFold soundness, point form**: public coordinates of a satisfied circuit are those of
genuine group elements related by `R = P₀ + ρ · P₁`. -/
theorem cf_sound_pts (hb : W.a₆ ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hnr : ∀ e : ZMod p, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) {n : ℕ} (hn : 1 ≤ n)
    (hrn : 2 ^ n < r) (hnp : 2 ^ n ≤ p) {G : ZMod p × ZMod p} (hG : W.toAffine.Equation G.1 G.2)
    {ρ p0x p0y p1x p1y rx ry : ZMod p} {w : CFWit (ZMod p)}
    (h : CFRel W n G ρ p0x p0y p1x p1y rx ry w) :
    ρ.val < 2 ^ n ∧ ∃ P0 P1 P2 : W.toAffine.Point,
      coordsOf W P0 = (p0x, p0y) ∧ coordsOf W P1 = (p1x, p1y) ∧ coordsOf W P2 = (rx, ry) ∧
      P2 = P0 + ρ.val • P1 := by
  obtain ⟨hρ, hv0, hv1, ha0, ha1, hsm, haR⟩ := h
  have hbool : ∀ i < n, IsBool (w.bits i) := fun i hi => hρ.1 ⟨i, hi⟩
  obtain ⟨hval, hlt⟩ := toNBits_sound hnp hρ
  rw [natVal_bitsOf] at hval
  obtain ⟨hS_c, hS_n, hS_p⟩ :=
    scalar_mul_sound W h2 hnr hord hn hrn hG hbool hv1.1 hsm
  obtain ⟨hR_c, hR_n, hR_p⟩ := rcb_spec W h2 hnr hS_c hv0.1 hS_n hv0.not_isZero
  refine ⟨hlt, w.P₀.pt W, w.P₁.pt W, (rcb W.a₄ W.a₆ (smOut W n G w.bits w.sm) w.P₀).pt W,
    coordsOf_pt_affine W hv0.1 ha0, coordsOf_pt_affine W hv1.1 ha1,
    coordsOf_pt_affine W hR_c haR, ?_⟩
  rw [hR_p, hS_p, hval, add_comm]

end Gadget
end Sonobe
