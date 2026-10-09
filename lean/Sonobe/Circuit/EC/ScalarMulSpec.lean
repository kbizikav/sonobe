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

/-- The value of the affine chunk of `fixed_scalar_mul_le`: accumulator minus the conditional
subtrahend, with the complete formula. -/
def smCore (n : ℕ) (Q : F × F) (bits : ℕ → F) (acc : ℕ → F × F) : PP F :=
  rcb W.a₄ W.a₆ (finPP (acc (n - 1))) (PP.neg (selPP (bits 0) zeroPP (finPP Q)))

/-- **The affine chunk computes `k · Q`** (`k` the integer of the first `n` bits) and leaves
`m n = 2ⁿ Q`. -/
theorem sm_core (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {q : W.toAffine.Point}
    (hq : addOrderOf q = r) {n : ℕ} (hn : 1 ≤ n) (hrn : 2 ^ n < r) {Q : F × F}
    (hE : W.toAffine.Equation Q.1 Q.2) (hQq : ptOf W Q = q) {bits : ℕ → F}
    (hb : ∀ i < n, IsBool (bits i)) {acc m tmp : ℕ → F × F} {lamA lamD : ℕ → F}
    (hC : ScalarChain W.a₄ n bits Q acc m tmp lamA lamD) :
    (smCore W n Q bits acc).OnCurve W.a₄ W.a₆ ∧ ¬ (smCore W n Q bits acc).IsZero ∧
      (smCore W n Q bits acc).pt W = natVal n (fun j => decide (bits j = 1)) • q ∧
      W.toAffine.Equation (m n).1 (m n).2 ∧ ptOf W (m n) = 2 ^ n • q := by
  obtain ⟨⟨hae, hap⟩, ⟨hme, hmp⟩⟩ := chain_sound W q hq h2 hnr hE hQq hrn hb hC (n - 1) (by omega)
  have hn' : n - 1 + 1 = n := by omega
  have hmn : W.toAffine.Equation (m n).1 (m n).2 ∧ ptOf W (m n) = 2 ^ n • q := by
    have hD : DblRel W.a₄ (m (n - 1)) (m n) (lamD (n - 1)) := by
      obtain ⟨-, -, hD0, hstep⟩ := hC
      rcases Nat.eq_zero_or_pos (n - 1) with h0 | h0
      · rw [h0]; rw [show n = 0 + 1 by omega]; exact hD0
      · have := (hstep (n - 1) h0 (by omega)).2.2
        rwa [hn'] at this
    have := dbl_step W q hq h2 hnr hme hmp hD
    rwa [hn'] at this
  have hres_c := finPP_onCurve W hae
  have hres_n := finPP_not_isZero (acc (n - 1))
  have hres_p : (finPP (acc (n - 1))).pt W = kv (fun j => if bits j = 1 then 1 else 0) (n - 1) • q := by
    rw [finPP_pt W hae, hap]
  have hb0 := hb 0 (by omega)
  have hsub_c : (PP.neg (selPP (bits 0) zeroPP (finPP Q))).OnCurve W.a₄ W.a₆ ∧
      ¬ (PP.neg (selPP (bits 0) zeroPP (finPP Q))).IsZero ∧
      (PP.neg (selPP (bits 0) zeroPP (finPP Q))).pt W = -((if bits 0 = 1 then 0 else 1) • q) := by
    rcases isBool_iff.mp hb0 with h0 | h0
    · rw [h0, selPP_zero, if_neg (by simp)]
      refine ⟨onCurve_neg.mpr (finPP_onCurve W hE), fun hh => finPP_not_isZero _ (isZero_neg.mp hh), ?_⟩
      rw [pt_neg, finPP_pt W hE, hQq, one_nsmul]
    · rw [h0, selPP_one, if_pos rfl]
      refine ⟨onCurve_neg.mpr (zeroPP_onCurve _ _), fun hh => zeroPP_not_isZero (isZero_neg.mp hh), ?_⟩
      rw [pt_neg, zeroPP_pt]; simp
  obtain ⟨hS_c, hS_n, hS_p⟩ := rcb_spec W h2 hnr hres_c hsub_c.1 hres_n hsub_c.2.1
  refine ⟨hS_c, hS_n, ?_, hmn⟩
  show (rcb W.a₄ W.a₆ _ _).pt W = _
  rw [hS_p, hres_p, hsub_c.2.2]
  have hk := natVal_succ_eq_kv bits (n - 1)
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
  · obtain ⟨hinf, -, -⟩ := hz0 hPz
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
    obtain ⟨c1, c2, c3, -⟩ := sm_core W h2 hnr (hord _ hq0) hn hrn hE hqP hb hC
    have hout : smOut W n G bits w = smCore W n (P.x / P.z, P.y / P.z) bits w.acc := by
      show selPP w.inf zeroPP (rcb W.a₄ W.a₆ (finPP (w.acc (n - 1)))
        (PP.neg (selPP (bits 0) zeroPP (finPP (selF w.inf G.1 w.x', selF w.inf G.2 w.y'))))) = _
      rw [show (selF w.inf G.1 w.x', selF w.inf G.2 w.y') = (P.x / P.z, P.y / P.z) from hQ, hinf,
        selPP_zero]
      rfl
    rw [hout]
    exact ⟨c1, c2, c3⟩

/-- One projective tail step: `res ← b ? res + m : res` with the complete formula. -/
theorem tail_step (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    {q : W.toAffine.Point} {S : PP F} {mm : F × F} {b : F} {k j : ℕ} (hb : IsBool b)
    (hS : S.OnCurve W.a₄ W.a₆) (hSn : ¬ S.IsZero) (hSp : S.pt W = k • q)
    (hm : W.toAffine.Equation mm.1 mm.2) (hmp : ptOf W mm = 2 ^ j • q) :
    (selPP b (rcb W.a₄ W.a₆ S (finPP mm)) S).OnCurve W.a₄ W.a₆ ∧
      ¬ (selPP b (rcb W.a₄ W.a₆ S (finPP mm)) S).IsZero ∧
      (selPP b (rcb W.a₄ W.a₆ S (finPP mm)) S).pt W =
        (k + if b = 1 then 2 ^ j else 0) • q := by
  obtain ⟨c, n, p⟩ := rcb_spec W h2 hnr hS (finPP_onCurve W hm) hSn (finPP_not_isZero mm)
  rcases isBool_iff.mp hb with h0 | h0
  · subst h0; simp only [selPP_zero]; simpa using ⟨hS, hSn, hSp⟩
  · subst h0; simp only [selPP_one]
    refine ⟨c, n, ?_⟩
    rw [p, hSp, finPP_pt W hm, hmp, add_nsmul]; simp

/-- Output of `scalar_mul_le` for a 254-bit scalar: 252 affine bits and two projective ones. -/
def smOut254 (G : F × F) (bits : ℕ → F) (w : SMWit F) : PP F :=
  let Q : F × F := (selF w.inf G.1 w.x', selF w.inf G.2 w.y')
  let S1 := smCore W 252 Q bits w.acc
  let S2 := selPP (bits 252) (rcb W.a₄ W.a₆ S1 (finPP (w.m 252))) S1
  let S3 := selPP (bits 253) (rcb W.a₄ W.a₆ S2 (finPP (w.m 253))) S2
  selPP w.inf zeroPP S3

/-- Constraints for a 254-bit scalar: the chain over bits `0…251` and the two extra doublings. -/
def SMRel254 (G : F × F) (bits : ℕ → F) (P : PP F) (w : SMWit F) : Prop :=
  ToAffineRel P w.x' w.y' w.inf w.zinv w.inv ∧
    ScalarChain W.a₄ 252 bits (selF w.inf G.1 w.x', selF w.inf G.2 w.y') w.acc w.m w.tmp
      w.lamA w.lamD ∧
    DblRel W.a₄ (w.m 252) (w.m 253) (w.lamD 252) ∧ DblRel W.a₄ (w.m 253) (w.m 254) (w.lamD 253)

theorem natVal_succ' (f : ℕ → Bool) (n : ℕ) :
    natVal (n + 1) f = natVal n f + if f n then 2 ^ n else 0 := by
  simp [natVal, Finset.sum_range_succ]

/-- **`scalar_mul_le` computes `ρ · P` for a 254-bit scalar** (needs `2^252 < r`). -/
theorem scalar_mul254_sound (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 252 < r)
    {G : F × F} {bits : ℕ → F} (hb : ∀ i < 254, IsBool (bits i)) {P : PP F}
    (hP : P.OnCurve W.a₄ W.a₆) {w : SMWit F} (h : SMRel254 W G bits P w) :
    (smOut254 W G bits w).OnCurve W.a₄ W.a₆ ∧ ¬ (smOut254 W G bits w).IsZero ∧
      (smOut254 W G bits w).pt W = natVal 254 (fun j => decide (bits j = 1)) • P.pt W := by
  obtain ⟨hA, hC, hD1, hD2⟩ := h
  obtain ⟨hz0, hz1⟩ := toAffine_sound hA
  by_cases hPz : P.z = 0
  · obtain ⟨hinf, -, -⟩ := hz0 hPz
    have hout : smOut254 W G bits w = zeroPP := by
      simp only [smOut254, hinf, selPP_one]
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
    have hq := hord _ hq0
    obtain ⟨c1, c2, c3, hm, hmp⟩ :=
      sm_core W h2 hnr hq (by norm_num) hrn hE hqP (fun i hi => hb i (by omega)) hC
    obtain ⟨hm3, hm3p⟩ := dbl_step W (P.pt W) hq h2 hnr hm hmp hD1
    obtain ⟨t1c, t1n, t1p⟩ := tail_step W h2 hnr (hb 252 (by norm_num)) c1 c2 c3 hm hmp
    obtain ⟨t2c, t2n, t2p⟩ := tail_step W h2 hnr (hb 253 (by norm_num)) t1c t1n t1p hm3 hm3p
    have hout : smOut254 W G bits w = selPP (bits 253)
        (rcb W.a₄ W.a₆ (selPP (bits 252) (rcb W.a₄ W.a₆ (smCore W 252 (P.x / P.z, P.y / P.z) bits w.acc)
          (finPP (w.m 252))) (smCore W 252 (P.x / P.z, P.y / P.z) bits w.acc)) (finPP (w.m 253)))
        (selPP (bits 252) (rcb W.a₄ W.a₆ (smCore W 252 (P.x / P.z, P.y / P.z) bits w.acc)
          (finPP (w.m 252))) (smCore W 252 (P.x / P.z, P.y / P.z) bits w.acc)) := by
      simp only [smOut254]
      rw [hQ, hinf, selPP_zero]
    rw [hout]
    refine ⟨t2c, t2n, ?_⟩
    rw [t2p]
    have e : natVal 254 (fun j => decide (bits j = 1)) =
        natVal 252 (fun j => decide (bits j = 1)) + (if bits 252 = 1 then 2 ^ 252 else 0) +
          (if bits 253 = 1 then 2 ^ 253 else 0) := by
      rw [show (254 : ℕ) = 252 + 1 + 1 by norm_num, natVal_succ', natVal_succ']
      simp
    rw [e]

end Sound

end Gadget
end Sonobe
