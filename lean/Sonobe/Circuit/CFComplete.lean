import Sonobe.Circuit.CFBridge
import Sonobe.Circuit.MulAdd
import Sonobe.Circuit.EC.ScalarMulComplete
import Sonobe.IVC.Completeness

/-!
**Completeness of the CycleFold circuit** (`Setup.CFComplete`): for every `P₂ = P₀ + ρ · P₁` with
`ρ < 2^128` the circuit has a satisfying assignment with public input `[ρ, P₀, P₁, P₂]`.

The witness is built gadget by gadget: bits of `ρ`, the points with `z = 1` (or `(0,1,0)` for the
identity), the `to_affine` witnesses, and the honest double-and-add chain.

Trusted: `Circuit.Compiles` in the direction `constraint model ⇒ R1CS satisfiable` (the model
mentions every Rust constraint that has a witness of its own; the remaining ones are determined by
it).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModCFC {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

section Points

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [Short W] [W.IsElliptic]

/-- A group element as the projective point of an honest witness: `(x, y, 1)`, or `(0, 1, 0)`. -/
noncomputable def ppOf : W.toAffine.Point → PP (ZMod p)
  | .zero => zeroPP
  | .some x y _ => finPP (x, y)

theorem ppOf_valid (hb : W.a₆ ≠ 0) (P : W.toAffine.Point) : ValidPP W (ppOf W P) := by
  cases P with
  | zero => exact ⟨zeroPP_onCurve _ _, by simp [ppOf, zeroPP]⟩
  | some x y h =>
    exact ⟨finPP_onCurve W ((equation_iff_nonsingular).mpr h), by simp [ppOf, finPP]⟩

theorem ppOf_pt (P : W.toAffine.Point) : (ppOf W P).pt W = P := by
  cases P with
  | zero => exact zeroPP_pt W
  | some x y h =>
    have hE : W.toAffine.Equation x y := (equation_iff_nonsingular).mpr h
    simp only [ppOf]
    rw [finPP_pt W hE, ptOf_eq W hE]
    rfl

/-- `to_affine` has a witness whose public output is the coordinates of the group element. -/
theorem toAffine_complete_coords {P : PP (ZMod p)} (hP : P.OnCurve W.a₄ W.a₆) :
    ∃ inf zinv inv, ToAffineRel P (coordsOf W (P.pt W)).1 (coordsOf W (P.pt W)).2 inf zinv inv := by
  obtain ⟨x, y, inf, zinv, inv, h⟩ := toAffine_complete P
  have := coordsOf_pt_affine W hP h
  rw [this]
  exact ⟨inf, zinv, inv, h⟩

end Points

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]
  (W : WeierstrassCurve (ZMod p2)) [Short W] [W.IsElliptic]
  {G2 S : Type*} [AddCommGroup G2] [Module (ZMod p2) G2]
  [Module (ZMod p1) W.toAffine.Point]

theorem cfComplete_of_circuit
    (T : Setup (ZMod p1) W.toAffine.Point (ZMod p2) G2 S (ZMod p2 × ZMod p2) 7)
    (hco : T.coords = coordsOf W)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hsmul : ∀ (n : ℕ) (P : W.toAffine.Point), (n : ZMod p1) • P = n • P)
    {G : ZMod p2 × ZMod p2} (hG : W.toAffine.Equation G.1 G.2)
    (circ : Circuit (ZMod p2) 7 T.nw2 (CFWit (ZMod p2))) (hcomp : circ.Compiles T.k2.r1cs)
    (hrel : ∀ x ω, circ.rel x ω ↔
      CFRel W 128 G (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    (hb : W.a₆ ≠ 0) (h2 : (2 : ZMod p2) ≠ 0)
    (hnr : ∀ e : ZMod p2, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r)
    (hrn : 2 ^ 128 < r) (hnp : 2 ^ 128 ≤ p2) : T.CFComplete := by
  intro n P0 P1 P2 hn hP
  have hval : ((n : ZMod p2)).val = n := ZMod.val_natCast_of_lt (lt_of_lt_of_le hn hnp)
  -- the bits of `ρ`
  obtain ⟨b, hbits⟩ := toNBits_complete (n := 128) (n : ZMod p2) (by rw [hval]; exact hn)
  set bits : ℕ → ZMod p2 := fun j => if h : j < 128 then b ⟨j, h⟩ else 0 with hbitsdef
  have hbitsFun : (fun i : Fin 128 => bits i) = b := by
    funext i; simp [hbitsdef, i.2]
  have hρ : ToNBitsRel 128 (n : ZMod p2) (fun i : Fin 128 => bits i) := by rw [hbitsFun]; exact hbits
  have hbool : ∀ i < 128, IsBool (bits i) := fun i hi => hρ.1 ⟨i, hi⟩
  have hnat : natVal 128 (fun j => decide (bits j = 1)) = n := by
    obtain ⟨hv, -⟩ := toNBits_sound hnp hρ
    rw [← natVal_bitsOf, ← hv, hval]
  -- the points
  have hv0 := ppOf_valid W hb P0
  have hv1 := ppOf_valid W hb P1
  obtain ⟨inf0, zinv0, inv0, ha0⟩ := toAffine_complete_coords W hv0.1
  obtain ⟨inf1, zinv1, inv1, ha1⟩ := toAffine_complete_coords W hv1.1
  rw [ppOf_pt] at ha0 ha1
  obtain ⟨wsm, hsm⟩ := sm_complete W h2 hnr hord (n := 128) (by norm_num) hrn hG hbool hv1.1
  obtain ⟨hR_c, hR_n, hR_p⟩ := mulAdd_spec W h2 hnr hord (n := 128) (by norm_num) hrn hG hbool
    hv1.1 hv0.1 (hv0.not_isZero W) hsm
  rw [ppOf_pt, hnat] at hR_p
  have hP2 : (rcb W.a₄ W.a₆ (smOut W 128 G bits wsm) (ppOf W P0)).pt W = P2 := by
    rw [hR_p, ppOf_pt, hP, hsmul]
  obtain ⟨infR, zinvR, invR, haR⟩ := toAffine_complete_coords W hR_c
  rw [hP2] at haR
  have hcf : CFRel W 128 G ((n : ZMod p2)) (coordsOf W P0).1 (coordsOf W P0).2 (coordsOf W P1).1
      (coordsOf W P1).2 (coordsOf W P2).1 (coordsOf W P2).2
      ⟨bits, ppOf W P0, ppOf W P1, inf0, zinv0, inv0, inf1, zinv1, inv1, wsm, infR, zinvR, invR⟩ :=
    ⟨hρ, hv0, hv1, ha0, ha1, hsm, haR⟩
  have hr := (hrel (cfVec n (coordsOf W P0) (coordsOf W P1) (coordsOf W P2)) _).mpr
    (by simpa [cfVec] using hcf)
  obtain ⟨w, hw⟩ := circ.sat_of_rel hcomp hr
  refine ⟨⟨w, 0⟩, ⟨T.k2.ckW.commit w 0, T.cfX n (T.coords P0) (T.coords P1) (T.coords P2)⟩,
    ⟨?_, rfl⟩, rfl⟩
  simpa [hco, hcfx] using hw

end Gadget
end Sonobe
