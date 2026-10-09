import Sonobe.Circuit.EC.ScalarMul
import Sonobe.Circuit.Bits

/-!
Full `ProjectiveVar::scalar_mul_le` gadget (short_weierstrass/mod.rs:505-560) for `n`
boolean scalar bits (`n ≤ MODULUS_BITS - 2`, so the projective tail is empty).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- `c ? t : f` for field elements. -/
def selF (c t f : F) : F := c * (t - f) + f

/-- Witnesses of one scalar multiplication gadget. -/
structure SMWit (F : Type*) where
  inf : F
  zinv : F
  inv : F
  x' : F
  y' : F
  acc : ℕ → F × F
  m : ℕ → F × F
  tmp : ℕ → F × F
  lamA : ℕ → F
  lamD : ℕ → F

/-- Output of the gadget in terms of its witnesses: the generator replaces an infinite base, the
LSB is handled by a conditional subtraction with the complete formula, and an infinite base gives
the zero point. -/
def smOut (n : ℕ) (G : F × F) (bits : ℕ → F) (w : SMWit F) : PP F :=
  let Q : F × F := (selF w.inf G.1 w.x', selF w.inf G.2 w.y')
  selPP w.inf zeroPP
    (rcb W.a₄ W.a₆ (finPP (w.acc (n - 1))) (PP.neg (selPP (bits 0) zeroPP (finPP Q))))

/-- Constraints of the gadget. -/
def SMRel (n : ℕ) (G : F × F) (bits : ℕ → F) (P : PP F) (w : SMWit F) : Prop :=
  ToAffineRel P w.x' w.y' w.inf w.zinv w.inv ∧
    ScalarChain W.a₄ n bits (selF w.inf G.1 w.x', selF w.inf G.2 w.y') w.acc w.m w.tmp
      w.lamA w.lamD

theorem natVal_succ_eq_kv (bits : ℕ → F) :
    ∀ i, natVal (i + 1) (fun j => decide (bits j = 1)) + 1 =
      (if bits 0 = 1 then 1 else 0) + kv (fun j => if bits j = 1 then 1 else 0) i
  | 0 => by
    by_cases h : bits 0 = 1 <;> simp [natVal, kv, h]
  | i + 1 => by
    have ih := natVal_succ_eq_kv bits i
    have e : natVal (i + 1 + 1) (fun j => decide (bits j = 1)) =
        natVal (i + 1) (fun j => decide (bits j = 1)) + (if bits (i + 1) = 1 then 2 ^ (i + 1) else 0) := by
      simp [natVal, Finset.sum_range_succ]
    rw [e, kv]
    by_cases h : bits (i + 1) = 1 <;> simp [h] <;> omega

section Sound

variable {r : ℕ}

/-- **`scalar_mul_le` computes `ρ · P`.** -/
theorem scalar_mul_sound (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r)
    {n : ℕ} (hn : 1 ≤ n) (hrn : 2 ^ n < r) {G : F × F} (hG : W.toAffine.Equation G.1 G.2)
    {bits : ℕ → F} (hb : ∀ i < n, IsBool (bits i)) {P : PP F} (hP : P.OnCurve W.a₄ W.a₆)
    {w : SMWit F} (h : SMRel W n G bits P w) :
    (smOut W n G bits w).OnCurve W.a₄ W.a₆ ∧ ¬ (smOut W n G bits w).IsZero ∧
      (smOut W n G bits w).pt W = natVal n (fun j => decide (bits j = 1)) • P.pt W := by
  obtain ⟨hA, hC⟩ := h
  obtain ⟨hz0, hz1⟩ := toAffine_sound hA
  by_cases hPz : P.z = 0
  · -- infinite base: the output is the zero point
    obtain ⟨hinf, -, -⟩ := hz0 hPz
    have hout : smOut W n G bits w = zeroPP := by
      simp only [smOut, hinf, selPP_one]
    rw [hout, pt_of_z_zero W hPz]
    exact ⟨zeroPP_onCurve _ _, zeroPP_not_isZero, by rw [zeroPP_pt]; simp⟩
  · obtain ⟨hinf, hx, hy⟩ := hz1 hPz
    have hQ : (selF w.inf G.1 w.x', selF w.inf G.2 w.y') = (P.x / P.z, P.y / P.z) := by
      simp [selF, hinf, hx, hy]
    rw [hQ] at hC
    have hE := equation_of_onCurve W hPz hP
    have hqP : ptOf W (P.x / P.z, P.y / P.z) = P.pt W := by
      rw [ptOf_eq W hE, pt_of_equation W hPz hE]
    have hq0 : P.pt W ≠ 0 := by
      rw [pt_of_equation W hPz hE]; exact Affine.Point.some_ne_zero _
    have hq : addOrderOf (P.pt W) = r := hord _ hq0
    obtain ⟨⟨hae, hap⟩, -⟩ := chain_sound W (P.pt W) hq h2 hnr hE hqP hrn hb hC (n - 1) (by omega)
    -- the accumulator and the conditional subtrahend are valid points
    have hres_c := finPP_onCurve W hae
    have hres_n := finPP_not_isZero (w.acc (n - 1))
    have hres_p : (finPP (w.acc (n - 1))).pt W = kv (fun j => if bits j = 1 then 1 else 0) (n - 1) •
        P.pt W := by rw [finPP_pt W hae, hap]
    have hb0 := hb 0 (by omega)
    have hsub_c : (PP.neg (selPP (bits 0) zeroPP (finPP (P.x / P.z, P.y / P.z)))).OnCurve W.a₄ W.a₆ ∧
        ¬ (PP.neg (selPP (bits 0) zeroPP (finPP (P.x / P.z, P.y / P.z)))).IsZero ∧
        (PP.neg (selPP (bits 0) zeroPP (finPP (P.x / P.z, P.y / P.z)))).pt W =
          -((if bits 0 = 1 then 0 else 1) • P.pt W) := by
      rcases isBool_iff.mp hb0 with h0 | h0
      · rw [h0, selPP_zero, if_neg (by simp)]
        refine ⟨onCurve_neg.mpr (finPP_onCurve W hE), fun hh => finPP_not_isZero _ (isZero_neg.mp hh), ?_⟩
        rw [pt_neg, finPP_pt W hE, hqP, one_nsmul]
      · rw [h0, selPP_one, if_pos rfl]
        refine ⟨onCurve_neg.mpr (zeroPP_onCurve _ _), fun hh => zeroPP_not_isZero (isZero_neg.mp hh), ?_⟩
        rw [pt_neg, zeroPP_pt]; simp
    obtain ⟨hS_c, hS_n, hS_p⟩ := rcb_spec W h2 hnr hres_c hsub_c.1 hres_n hsub_c.2.1
    have hout : smOut W n G bits w =
        rcb W.a₄ W.a₆ (finPP (w.acc (n - 1)))
          (PP.neg (selPP (bits 0) zeroPP (finPP (P.x / P.z, P.y / P.z)))) := by
      show selPP w.inf zeroPP (rcb W.a₄ W.a₆ (finPP (w.acc (n - 1)))
        (PP.neg (selPP (bits 0) zeroPP (finPP (selF w.inf G.1 w.x', selF w.inf G.2 w.y'))))) = _
      rw [show (selF w.inf G.1 w.x', selF w.inf G.2 w.y') = (P.x / P.z, P.y / P.z) from hQ, hinf,
        selPP_zero]
    rw [hout]
    refine ⟨hS_c, hS_n, ?_⟩
    rw [hS_p, hres_p, hsub_c.2.2]
    have hk := natVal_succ_eq_kv bits (n - 1)
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at hk
    rcases isBool_iff.mp hb0 with h0 | h0
    · have e : (if bits 0 = 1 then 0 else 1 : ℕ) = 1 := by simp [h0]
      have e' : (if bits 0 = 1 then 1 else 0 : ℕ) = 0 := by simp [h0]
      rw [e'] at hk
      rw [e]
      have : kv (fun j => if bits j = 1 then 1 else 0) (n - 1) =
          natVal n (fun j => decide (bits j = 1)) + 1 := by omega
      rw [this, succ_nsmul, one_nsmul]; abel
    · have e : (if bits 0 = 1 then 0 else 1 : ℕ) = 0 := by simp [h0]
      have e' : (if bits 0 = 1 then 1 else 0 : ℕ) = 1 := by simp [h0]
      rw [e'] at hk
      rw [e]
      have : kv (fun j => if bits j = 1 then 1 else 0) (n - 1) =
          natVal n (fun j => decide (bits j = 1)) := by omega
      rw [this]; simp

end Sound

end Gadget
end Sonobe
