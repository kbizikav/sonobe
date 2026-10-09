import Sonobe.Circuit.Emulated.Absorb
import Sonobe.Circuit.Emulated.Canon
import Sonobe.Circuit.CycleFold
import Sonobe.Commitment.Pedersen

/-!
The secondary Pedersen opening of the decider circuit (`PedersenGadget<C2, true>::open`,
primitives/src/commitments/pedersen.rs:277-293), with constant generators:

```
gv = Σ_i g_i.scalar_mul_le(v_i.to_bits_le())        -- msm, starting from the constant zero
hr = h.scalar_mul_le(r.to_bits_le())
(gv + hr).enforce_equal(cm)
```
`to_bits_le` of an emulated variable concatenates the limb bits (7 × 32, then 30).
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

/-- All group-law lemmas are stated with the classical `DecidableEq`. -/
noncomputable local instance (priority := 10000) decEqZModPO {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

section Bits

variable {p : ℕ} [Fact p.Prime]

/-- Bit `j` of the concatenated limb bits `to_bits_le` of an emulated variable. -/
def ebit (w : AbsWit p) (j : ℕ) : ZMod p :=
  if h : j < 224 then w.bl (j / 32) ⟨j % 32, Nat.mod_lt _ (by norm_num)⟩
  else if h2 : j - 224 < 30 then w.bt ⟨j - 224, h2⟩ else 0

/-- Limb-bit constraints of `to_bits_le`. -/
def EmuBitsRel (a : ℕ → ZMod p) (w : AbsWit p) : Prop :=
  (∀ i < 7, ToNBitsRel 32 (a i) (w.bl i)) ∧ ToNBitsRel 30 (a 7) w.bt

theorem ebit_dec (w : AbsWit p) {j : ℕ} (hj : j < 254) :
    decide (ebit w j = 1) = catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) j := by
  unfold ebit catBit
  by_cases h : j < 224
  · simp only [h, dif_pos, if_true, bitsOf]
    rw [dif_pos (Nat.mod_lt _ (by norm_num))]
    exact decide_eq_decide.mpr Iff.rfl
  · have h2 : j - 224 < 30 := by omega
    simp only [h, dif_neg, if_false, h2, dif_pos, bitsOf, not_false_eq_true]
    exact decide_eq_decide.mpr Iff.rfl

theorem ebit_bool {a : ℕ → ZMod p} {w : AbsWit p} (h : EmuBitsRel a w) {j : ℕ} (hj : j < 254) :
    IsBool (ebit w j) := by
  obtain ⟨hl, ht⟩ := h
  unfold ebit
  by_cases h1 : j < 224
  · rw [dif_pos h1]; exact (hl (j / 32) (by omega)).1 _
  · have h2 : j - 224 < 30 := by omega
    rw [dif_neg h1, dif_pos h2]; exact ht.1 _

/-- **`to_bits_le` of an emulated variable is the binary expansion of its value.** -/
theorem ebit_val (h32 : 2 ^ 32 ≤ p) {a : ℕ → ZMod p} {w : AbsWit p} (h : EmuBitsRel a w) :
    natVal 254 (fun j => decide (ebit w j = 1)) = limbsVal 8 a := by
  obtain ⟨hl, ht⟩ := h
  have hnat : natVal 254 (fun j => decide (ebit w j = 1)) =
      natVal 254 (catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt)) := by
    unfold natVal
    refine sum_congr rfl fun j hj => ?_
    beta_reduce
    rw [ebit_dec w (mem_range.mp hj)]
  rw [hnat]
  generalize hg : catBit (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) = g
  have hL : ∀ i < 7, natVal 32 (fun t => bitsOf (w.bl i) t) = (a i).val := fun i hi =>
    ((toNBits_sound h32 (hl i hi)).1).symm
  have hT : natVal 30 (bitsOf w.bt) = (a 7).val := by
    have h30 : 2 ^ 30 ≤ p := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) h32
    exact ((toNBits_sound h30 ht).1).symm
  have e1 : natVal 224 g = ∑ i ∈ range 7, natVal 32 (fun t => bitsOf (w.bl i) t) * 2 ^ (32 * i) := by
    have := natVal_cat (fun i t => bitsOf (w.bl i) t) (bitsOf w.bt) 7 le_rfl
    rw [hg] at this
    simpa only [Nat.reduceMul] using this
  have e2 : natVal (224 + 30) g = natVal 224 g + 2 ^ 224 * natVal 30 (fun j => g (224 + j)) :=
    natVal_add g 224 30
  have e3 : natVal 30 (fun j => g (224 + j)) = natVal 30 (bitsOf w.bt) := by
    unfold natVal
    refine sum_congr rfl fun j hj => ?_
    have : ¬ (224 + j < 224) := by omega
    simp [← hg, catBit, this]
  have e5 : natVal 254 g = natVal (224 + 30) g := by simp only [Nat.reduceAdd]
  symm
  rw [e5, e2, e3, e1, hT]
  unfold limbsVal
  rw [show (8 : ℕ) = 7 + 1 by norm_num, sum_range_succ]
  have hs : ∑ i ∈ range 7, natVal 32 (fun t => bitsOf (w.bl i) t) * 2 ^ (32 * i) =
      ∑ i ∈ range 7, (a i).val * 2 ^ (32 * i) :=
    sum_congr rfl fun i hi => by rw [hL i (mem_range.mp hi)]
  rw [hs]
  norm_num
  ring

end Bits

section EC

variable {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p)) [Short W] [W.IsElliptic]

/-- `ProjectiveVar::enforce_equal`: both at infinity, or equal after cross-multiplication. -/
def PPEqRel (P Q : PP (ZMod p)) : Prop :=
  (P.z = 0 ∧ Q.z = 0) ∨ (P.x * Q.z = Q.x * P.z ∧ P.y * Q.z = Q.y * P.z)

/-- `enforce_equal` on valid points is equality of group elements. -/
theorem ppEq_pt {P Q : PP (ZMod p)} (hP : P.OnCurve W.a₄ W.a₆) (hQ : Q.OnCurve W.a₄ W.a₆)
    (nP : ¬ P.IsZero) (nQ : ¬ Q.IsZero) (h : PPEqRel P Q) : P.pt W = Q.pt W := by
  rcases h with ⟨hz1, hz2⟩ | ⟨hx, hy⟩
  · rw [pt_of_z_zero W hz1, pt_of_z_zero W hz2]
  · by_cases hz1 : P.z = 0 <;> by_cases hz2 : Q.z = 0
    · rw [pt_of_z_zero W hz1, pt_of_z_zero W hz2]
    · exfalso
      rw [hz1, mul_zero] at hx hy
      exact nP ⟨(mul_eq_zero.mp hx).resolve_right hz2, (mul_eq_zero.mp hy).resolve_right hz2, hz1⟩
    · exfalso
      rw [hz2, mul_zero] at hx hy
      exact nQ ⟨(mul_eq_zero.mp hx.symm).resolve_right hz1, (mul_eq_zero.mp hy.symm).resolve_right hz1, hz2⟩
    · have e1 : P.x / P.z = Q.x / Q.z := by field_simp; linear_combination hx
      have e2 : P.y / P.z = Q.y / Q.z := by field_simp; linear_combination hy
      have hEP := equation_of_onCurve W hz1 hP
      have hEQ := equation_of_onCurve W hz2 hQ
      rw [pt_of_equation W hz1 hEP, pt_of_equation W hz2 hEQ]
      simp only [e1, e2]

end EC

section Open

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]
  (W : WeierstrassCurve (ZMod p1)) [Short W] [W.IsElliptic]

/-- Witnesses of one Pedersen opening: limb bits and scalar-multiplication witnesses. -/
structure OpenWit (p : ℕ) where
  aw : ℕ → AbsWit p
  sm : ℕ → SMWit (ZMod p)
  rw_ : AbsWit p
  smh : SMWit (ZMod p)

/-- `msm`: `res = 0; res += g_i · v_i`. -/
def msmOut (G : ZMod p1 × ZMod p1) (w : OpenWit p1) : ℕ → PP (ZMod p1)
  | 0 => zeroPP
  | k + 1 => rcb W.a₄ W.a₆ (msmOut G w k) (smOut254 W G (ebit (w.aw k)) (w.sm k))

/-- Constraints of `PedersenGadget<C2, true>::open` with `n` constant generators `g`, constant
`h`, scalar limbs `a i` and `r`, and the commitment `cm`. -/
def OpenRel (n : ℕ) (G : ZMod p1 × ZMod p1) (g : ℕ → PP (ZMod p1)) (h : PP (ZMod p1))
    (a : ℕ → ℕ → ZMod p1) (r : ℕ → ZMod p1) (cm : PP (ZMod p1)) (w : OpenWit p1) : Prop :=
  (∀ i < n, EmuBitsRel (a i) (w.aw i) ∧ SMRel254 W G (ebit (w.aw i)) (g i) (w.sm i)) ∧
  EmuBitsRel r w.rw_ ∧ SMRel254 W G (ebit w.rw_) h w.smh ∧
  PPEqRel (rcb W.a₄ W.a₆ (msmOut W G w n) (smOut254 W G (ebit w.rw_) w.smh)) cm

theorem msm_sound (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    {r : ℕ} (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 252 < r)
    (h32 : 2 ^ 32 ≤ p1) {G : ZMod p1 × ZMod p1} {w : OpenWit p1} {n : ℕ}
    {g : ℕ → PP (ZMod p1)} {a : ℕ → ℕ → ZMod p1} (hg : ∀ i < n, (g i).OnCurve W.a₄ W.a₆)
    (h : ∀ i < n, EmuBitsRel (a i) (w.aw i) ∧ SMRel254 W G (ebit (w.aw i)) (g i) (w.sm i)) :
    ∀ k ≤ n, (msmOut W G w k).OnCurve W.a₄ W.a₆ ∧ ¬ (msmOut W G w k).IsZero ∧
      (msmOut W G w k).pt W = ∑ i ∈ range k, limbsVal 8 (a i) • (g i).pt W
  | 0, _ => by
    refine ⟨zeroPP_onCurve _ _, zeroPP_not_isZero, ?_⟩
    simp [msmOut, zeroPP_pt]
  | k + 1, hk => by
    obtain ⟨c, nz, e⟩ := msm_sound h2 hnr hord hrn h32 hg h k (by omega)
    obtain ⟨hb, hs⟩ := h k (by omega)
    obtain ⟨c2, n2, e2⟩ := scalar_mul254_sound W h2 hnr hord hrn
      (fun j hj => ebit_bool hb hj) (hg k (by omega)) hs
    obtain ⟨c3, n3, e3⟩ := rcb_spec W h2 hnr c c2 nz n2
    refine ⟨c3, n3, ?_⟩
    show (rcb W.a₄ W.a₆ _ _).pt W = _
    rw [e3, e, e2, ebit_val h32 hb, sum_range_succ]

/-- **The secondary Pedersen opening gadget is the Pedersen commitment.** -/
theorem open_sound [Module (ZMod p2) W.toAffine.Point]
    (hsmul : ∀ (n : ℕ) (P : W.toAffine.Point), (n : ZMod p2) • P = n • P)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    {r : ℕ} (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 252 < r)
    (h32 : 2 ^ 32 ≤ p1) {G : ZMod p1 × ZMod p1} {w : OpenWit p1} {n : ℕ}
    {g : ℕ → PP (ZMod p1)} {hh : PP (ZMod p1)} {a : ℕ → ℕ → ZMod p1} {rr : ℕ → ZMod p1}
    {cm : PP (ZMod p1)} (hg : ∀ i < n, (g i).OnCurve W.a₄ W.a₆) (hhc : hh.OnCurve W.a₄ W.a₆)
    (hcm : ValidPP W cm) (h : OpenRel W n G g hh a rr cm w) :
    (PedersenKey.mk (F := ZMod p2) (fun i : Fin n => (g i).pt W) (hh.pt W)).Opens
      (fun i => emuV p2 (a i)) (emuV p2 rr) (cm.pt W) := by
  obtain ⟨hterms, hrb, hrs, heq⟩ := h
  obtain ⟨c, nz, e⟩ := msm_sound W h2 hnr hord hrn h32 hg hterms n le_rfl
  obtain ⟨c2, n2, e2⟩ := scalar_mul254_sound W h2 hnr hord hrn
    (fun j hj => ebit_bool hrb hj) hhc hrs
  obtain ⟨c3, n3, e3⟩ := rcb_spec W h2 hnr c c2 nz n2
  have := ppEq_pt W c3 hcm.1 n3 (hcm.not_isZero W) heq
  unfold PedersenKey.Opens PedersenKey.commit
  rw [← this, e3, e, e2, ebit_val h32 hrb]
  simp only [emuV, hsmul]
  rw [← Fin.sum_univ_eq_sum_range (fun i => limbsVal 8 (a i) • (g i).pt W) n]

end Open

end Gadget
end Sonobe
