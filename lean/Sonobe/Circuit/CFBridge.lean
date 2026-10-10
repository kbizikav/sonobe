import Sonobe.Circuit.Coords
import Sonobe.IVC.Soundness

/-!
Bridge: the CycleFold circuit constraints (`CFRel`) imply `Setup.CFSound`.

Trusted: `Circuit.Compiles` (the R1CS of the secondary decider key is the circuit's constraint
system), and the identification of the abstract `coords`/`cfX` with affine coordinates and the public
input order `[ρ, P₀.x, P₀.y, P₁.x, P₁.y, R.x, R.y]` (adapters/nova.rs:94-126).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModB {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

/-- The public input vector of a CycleFold circuit. -/
def cfVec {p : ℕ} (n : ℕ) (c0 c1 c2 : ZMod p × ZMod p) : Fin 7 → ZMod p :=
  ![(n : ZMod p), c0.1, c0.2, c1.1, c1.2, c2.1, c2.2]

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]
  (W : WeierstrassCurve (ZMod p2)) [Short W] [W.IsElliptic]
  {G2 S : Type*} [AddCommGroup G2] [Module (ZMod p2) G2]
  [Module (ZMod p1) W.toAffine.Point]

theorem cfSound_of_circuit
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
    (hrn : 2 ^ 128 < r) (hnp : 2 ^ 128 ≤ p2) : T.CFSound := by
  intro cw cu hinc n c0 c1 c2 hn hx
  have hrel' := (hrel _ _).mp (circ.rel_of_sat hcomp hinc.1)
  rw [hx, hcfx] at hrel'
  obtain ⟨hlt, P0, P1, P2, e0, e1, e2, hP⟩ := cf_sound_pts W hb h2 hnr hord (by norm_num) hrn hnp hG
    (by simpa [cfVec] using hrel')
  have hval : ((n : ZMod p2)).val = n := ZMod.val_natCast_of_lt (lt_of_lt_of_le hn hnp)
  refine ⟨P0, P1, P2, ?_, ?_, ?_, ?_⟩
  · rw [hco]; simpa [cfVec] using e0
  · rw [hco]; simpa [cfVec] using e1
  · rw [hco]; simpa [cfVec] using e2
  · rw [hsmul, ← hval]; simpa [cfVec, hval] using hP

end Gadget
end Sonobe
