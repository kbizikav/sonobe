import Sonobe.Circuit.FS2
import Sonobe.Circuit.EC.ScalarMulComplete

/-!
Completeness of the secondary fold gadget `FS2::Gadget::verify` (`FS2Rel`): for canonical,
valid inputs and boolean challenge bits the gadget has a witness.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

noncomputable local instance decEqZModFS2C {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- **Assumption (completeness half of `EmuArith`)**: the emulated `modulo` additions and
multiplications have a witness for canonical inputs. -/
structure EmuArith.Complete (EA : EmuArith p1 p2) : Prop where
  add_complete : ∀ a b, Canon p2 a → (∀ k < 4, (b k).val < 2 ^ 32) → (∀ k, 4 ≤ k → b k = 0) →
    ∃ o, EA.ModAdd a b o
  mul_complete : ∀ a b c, Canon p2 a → Canon p2 c → (∀ k < 4, (b k).val < 2 ^ 32) →
    (∀ k, 4 ≤ k → b k = 0) → ∃ o, EA.ModMulAdd a b c o

variable (W : WeierstrassCurve (ZMod p1)) [Short W] [W.IsElliptic]

theorem fs2_complete (EA : EmuArith p1 p2) (hEA : EA.Complete) (h2 : (2 : ZMod p1) ≠ 0)
    (hnr : ∀ e : ZMod p1, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0) {r : ℕ}
    (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) (hrn : 2 ^ 128 < r)
    (h32 : 2 ^ 32 < p1) {G : ZMod p1 × ZMod p1} (hG : W.toAffine.Equation G.1 G.2)
    {U : SecVar (ZMod p1)} {I : SecInc (ZMod p1)} {π : PP (ZMod p1)} {bits : ℕ → ZMod p1}
    (hb : ∀ j < 128, IsBool (bits j))
    (hUu : Canon p2 U.u) (hUx : ∀ j, Canon p2 (U.x j)) (hIx : ∀ j, Canon p2 (I.x j))
    (hUE : ValidPP W U.cmE) (hUW : ValidPP W U.cmW) (hIW : ValidPP W I.cmW)
    (hπ : π.OnCurve W.a₄ W.a₆) :
    ∃ O : SecVar (ZMod p1), FS2Rel W EA G U I π bits O := by
  obtain ⟨hr1, hr2, hr3⟩ := rhoLimbs_val h32 bits hb
  obtain ⟨ou, hou⟩ := hEA.add_complete _ _ hUu hr1 hr2
  have hox : ∀ j, ∃ o, EA.ModMulAdd (I.x j) (rhoLimbs bits) (U.x j) o := fun j =>
    hEA.mul_complete _ _ _ (hIx j) (hUx j) hr1 hr2
  choose ox hox using hox
  obtain ⟨wA, hA⟩ := sm_complete W h2 hnr hord (n := 128) (by norm_num) hrn hG
    (fun j hj => hb j hj) hπ
  obtain ⟨wB, hB⟩ := sm_complete W h2 hnr hord (n := 128) (by norm_num) hrn hG
    (fun j hj => hb j hj) hIW.1
  exact ⟨⟨ou, ox, rcb W.a₄ W.a₆ (smOut W 128 G bits wA) U.cmE,
    rcb W.a₄ W.a₆ (smOut W 128 G bits wB) U.cmW⟩, fun j hj => hb j hj, hou, hox, wA, wB, hA, hB,
    rfl, rfl⟩

end Gadget
end Sonobe
