import Sonobe.Circuit.MulAdd
import Sonobe.Circuit.Coords
import Sonobe.Circuit.Emulated.Canon
import Sonobe.IVC.Model

/-!
The secondary folding-scheme verifier gadget (`FS2::Gadget::verify`, fs/src/nova/circuits/verifier.rs
:112-139), inside the augmented circuit over `F = ZMod p1` with emulated scalars `E = ZMod p2`:

```
rho   = ScalarVar::from_bits_le(rho_bits)                   -- 4 limbs, value < 2^128
u'    = (U.u + rho).try_into()                              -- emulated add + modulo
x'_j  = (u.x_j * rho + U.x_j).try_into()                    -- emulated mul/add + modulo
cm_e' = proof.scalar_mul_le(rho_bits) + U.cm_e              -- native curve gadget over G2
cm_w' = u.cm_w.scalar_mul_le(rho_bits) + U.cm_w
```

The emulated modulo arithmetic is the single explicit assumption `EmuArith` (the user-approved
scope: canonical allocation, `enforce_lt` and the carry lifting are proved in `Circuit/Emulated`, the
operation-specific static-bound argument for `modulo` is assumed).
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

noncomputable local instance decEqZModFS2 {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

/-- Limbs of `from_bits_le(bits)` for a 128-bit challenge (four limbs of 32 bits, rest zero). -/
def rhoLimbs {p : ℕ} (bits : ℕ → ZMod p) : ℕ → ZMod p :=
  fun k => if k < 4 then ∑ t ∈ range 32, bits (32 * k + t) * 2 ^ t else 0

/-- The emulated arithmetic gadgets (`add_unaligned`/`mul_unaligned` + `modulo`) as an interface:
constraint predicates and the statement that they are sound for canonical inputs. -/
structure EmuArith (p1 p2 : ℕ) [Fact p1.Prime] where
  ModAdd : (ℕ → ZMod p1) → (ℕ → ZMod p1) → (ℕ → ZMod p1) → Prop
  ModMulAdd : (ℕ → ZMod p1) → (ℕ → ZMod p1) → (ℕ → ZMod p1) → (ℕ → ZMod p1) → Prop
  add_sound : ∀ a b o, Canon p2 a → (∀ k < 4, (b k).val < 2 ^ 32) → (∀ k, 4 ≤ k → b k = 0) →
    ModAdd a b o → Canon p2 o ∧ (limbsVal 8 o : ℕ) = (limbsVal 8 a + limbsVal 8 b) % p2
  mul_sound : ∀ a b c o, Canon p2 a → Canon p2 c → (∀ k < 4, (b k).val < 2 ^ 32) →
    (∀ k, 4 ≤ k → b k = 0) → ModMulAdd a b c o →
      Canon p2 o ∧ (limbsVal 8 o : ℕ) = (limbsVal 8 a * limbsVal 8 b + limbsVal 8 c) % p2

theorem natVal_blocks (f : ℕ → Bool) :
    ∀ k, natVal (32 * k) f = ∑ i ∈ range k, natVal 32 (fun t => f (32 * i + t)) * 2 ^ (32 * i)
  | 0 => by simp [natVal]
  | k + 1 => by
    rw [sum_range_succ, ← natVal_blocks f k, show 32 * (k + 1) = 32 * k + 32 by ring, natVal_add]
    ring

variable {p : ℕ} [Fact p.Prime]

theorem sum_bits_cast (bits : ℕ → ZMod p) (n : ℕ) (hb : ∀ j < n, IsBool (bits j)) :
    ∑ t ∈ range n, bits t * 2 ^ t = ((natVal n (fun t => decide (bits t = 1)) : ℕ) : ZMod p) := by
  unfold natVal
  push_cast
  refine sum_congr rfl fun t ht => ?_
  rcases isBool_iff.mp (hb t (mem_range.mp ht)) with h | h <;> simp [h]

/-- The value of the limbs of a boolean 128-bit challenge. -/
theorem rhoLimbs_val (h32 : 2 ^ 32 < p) (bits : ℕ → ZMod p) (hb : ∀ j < 128, IsBool (bits j)) :
    (∀ k < 4, (rhoLimbs bits k).val < 2 ^ 32) ∧ (∀ k, 4 ≤ k → rhoLimbs bits k = 0) ∧
      limbsVal 8 (rhoLimbs bits) = natVal 128 (fun j => decide (bits j = 1)) := by
  have hk : ∀ k < 4, (rhoLimbs bits k).val = natVal 32 (fun t => decide (bits (32 * k + t) = 1)) := by
    intro k hk
    have e : rhoLimbs bits k = ((natVal 32 (fun t => decide (bits (32 * k + t) = 1)) : ℕ) : ZMod p) := by
      simp only [rhoLimbs, if_pos hk]
      exact sum_bits_cast (fun t => bits (32 * k + t)) 32 (fun t ht => hb _ (by omega))
    rw [e]
    exact ZMod.val_natCast_of_lt (lt_trans (natVal_lt _ _) h32)
  refine ⟨fun k hk' => by rw [hk k hk']; exact natVal_lt _ _, fun k hk' => by simp [rhoLimbs]; omega, ?_⟩
  unfold limbsVal
  rw [show (8 : ℕ) = 4 + 4 by norm_num, sum_range_add]
  have h1 : ∑ i ∈ range 4, (rhoLimbs bits i).val * 2 ^ (32 * i) =
      natVal (32 * 4) (fun j => decide (bits j = 1)) := by
    rw [natVal_blocks]
    exact sum_congr rfl fun i hi => by rw [hk i (mem_range.mp hi)]
  have h2 : ∑ x ∈ range 4, (rhoLimbs bits (4 + x)).val * 2 ^ (32 * (4 + x)) = 0 := by
    refine sum_eq_zero fun x _ => ?_
    have : rhoLimbs bits (4 + x) = 0 := by simp [rhoLimbs]
    simp [this]
  rw [h2, add_zero, h1]

/-! ### The gadget -/

/-- Secondary running instance variable: emulated `u`, `x₀..x₆`, native points. -/
structure SecVar (F : Type*) where
  u : ℕ → F
  x : Fin 7 → ℕ → F
  cmE : PP F
  cmW : PP F

structure SecInc (F : Type*) where
  x : Fin 7 → ℕ → F
  cmW : PP F

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]
  (W : WeierstrassCurve (ZMod p1)) [Short W] [W.IsElliptic]
  {G2 : Type*} [AddCommGroup G2] [Module (ZMod p2) G2]

/-- Constraints of `FS2::Gadget::verify` for one fold. -/
def FS2Rel (EA : EmuArith p1 p2) (G : ZMod p1 × ZMod p1) (U : SecVar (ZMod p1))
    (I : SecInc (ZMod p1)) (π : PP (ZMod p1)) (bits : ℕ → ZMod p1) (O : SecVar (ZMod p1)) :
    Prop :=
  (∀ j < 128, IsBool (bits j)) ∧ EA.ModAdd U.u (rhoLimbs bits) O.u ∧
    (∀ j, EA.ModMulAdd (I.x j) (rhoLimbs bits) (U.x j) (O.x j)) ∧
    ∃ wA wB : SMWit (ZMod p1), SMRel W 128 G bits π wA ∧ SMRel W 128 G bits I.cmW wB ∧
      O.cmE = rcb W.a₄ W.a₆ (smOut W 128 G bits wA) U.cmE ∧
      O.cmW = rcb W.a₄ W.a₆ (smOut W 128 G bits wB) U.cmW

omit [Fact p2.Prime] in
theorem validPP_of {P : PP (ZMod p1)} (h : P.OnCurve W.a₄ W.a₆) (hn : ¬ P.IsZero) :
    ValidPP W P := by
  refine ⟨h, fun ⟨hy, hz⟩ => hn ⟨x_zero_of_z_zero W h hz, hy, hz⟩⟩

open Sonobe.Nova in
/-- Interpretation of the circuit variables as a model instance. -/
noncomputable def SecVar.val (U : SecVar (ZMod p1)) :
    RunningInstance (ZMod p2) W.toAffine.Point 7 :=
  ⟨U.cmE.pt W, emuV p2 U.u, U.cmW.pt W, fun j => emuV p2 (U.x j)⟩

open Sonobe.Nova in
noncomputable def SecInc.val (I : SecInc (ZMod p1)) :
    IncomingInstance W.toAffine.Point (ZMod p2) 7 :=
  ⟨I.cmW.pt W, fun j => emuV p2 (I.x j)⟩

open Sonobe.Nova in
/-- **The secondary fold gadget computes `foldInstance`.** -/
theorem fs2_sound [Module (ZMod p2) W.toAffine.Point]
    (hsmul : ∀ (n : ℕ) (P : W.toAffine.Point), (n : ZMod p2) • P = n • P)
    (EA : EmuArith p1 p2) (h2 : (2 : ZMod p1) ≠ 0)
    (hnr : ∀ e : ZMod p1, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (h32 : 2 ^ 32 < p1) {G : ZMod p1 × ZMod p1} (hG : W.toAffine.Equation G.1 G.2)
    {U : SecVar (ZMod p1)} {I : SecInc (ZMod p1)} {π : PP (ZMod p1)} {bits : ℕ → ZMod p1}
    {O : SecVar (ZMod p1)}
    (hUu : Canon p2 U.u) (hUx : ∀ j, Canon p2 (U.x j)) (hIx : ∀ j, Canon p2 (I.x j))
    (hUE : ValidPP W U.cmE) (hUW : ValidPP W U.cmW) (hIW : ValidPP W I.cmW)
    (hπ : π.OnCurve W.a₄ W.a₆) (h : FS2Rel W EA G U I π bits O) :
    Canon p2 O.u ∧ (∀ j, Canon p2 (O.x j)) ∧ ValidPP W O.cmE ∧ ValidPP W O.cmW ∧
      O.val W = foldInstance ((natVal 128 (fun j => decide (bits j = 1)) : ℕ) : ZMod p2)
        (π.pt W) (U.val W) (I.val W) := by
  obtain ⟨hb, hadd, hmul, wA, wB, hA, hB, hOE, hOW⟩ := h
  obtain ⟨hr1, hr2, hr3⟩ := rhoLimbs_val h32 bits hb
  obtain ⟨hOu, hOuv⟩ := EA.add_sound _ _ _ hUu hr1 hr2 hadd
  have hOx : ∀ j, Canon p2 (O.x j) ∧ (limbsVal 8 (O.x j) : ℕ) =
      (limbsVal 8 (I.x j) * limbsVal 8 (rhoLimbs bits) + limbsVal 8 (U.x j)) % p2 :=
    fun j => EA.mul_sound _ _ _ _ (hIx j) (hUx j) hr1 hr2 (hmul j)
  obtain ⟨cE, nE, pE⟩ := mulAdd_spec W h2 hnr hord (by norm_num) hrn hG (fun j hj => hb j hj) hπ hUE.1
    (hUE.not_isZero W) hA
  obtain ⟨cW, nW, pW⟩ := mulAdd_spec W h2 hnr hord (by norm_num) hrn hG (fun j hj => hb j hj) hIW.1
    hUW.1 (hUW.not_isZero W) hB
  generalize hρ : natVal 128 (fun j => decide (bits j = 1)) = ρ at hr3 pE pW ⊢
  refine ⟨hOu, fun j => (hOx j).1, by rw [hOE]; exact validPP_of W cE nE,
    by rw [hOW]; exact validPP_of W cW nW, ?_⟩
  simp only [SecVar.val, SecInc.val, foldInstance, RunningInstance.mk.injEq]
  have eu : emuV p2 O.u = emuV p2 U.u + (ρ : ZMod p2) := by
    unfold emuV
    rw [hOuv, ZMod.natCast_mod, Nat.cast_add, hr3, add_comm]
  have ex : ∀ j, emuV p2 (O.x j) = emuV p2 (U.x j) + (ρ : ZMod p2) * emuV p2 (I.x j) := by
    intro j
    unfold emuV
    rw [(hOx j).2, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, hr3]; ring
  refine ⟨?_, eu, ?_, ?_⟩
  · rw [hOE, pE, hsmul]
  · rw [hOW, pW, hsmul]
  · funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact ex j

end Gadget
end Sonobe
