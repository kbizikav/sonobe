import Sonobe.Circuit.EmuArithConcrete
import Sonobe.FinalSoundness
import Sonobe.Circuit.AugComplete
import Sonobe.IVC.Completeness

/-!
**IVC completeness with the circuit assumptions derived.**

`IVC.ivc_complete` assumed `AugComplete` and `CFComplete`, statements about the existence of
satisfying assignments of the augmented and the CycleFold circuit. Here both are *derived* from
the constraint-level models, exactly as `FinalSoundness` does for the soundness side:

* `Gadget.cfComplete_of_circuit` — the honest witness of `verify_point_rlc`;
* `Gadget.augComplete_of_circuit` — the honest witness of the augmented circuit, including the
  Fiat–Shamir derivation of both secondary challenges.

Trusted in addition to the soundness-side assumptions: the *completeness* direction of the R1CS
synthesis (`constraint model ⇒ R1CS satisfiable`), the completeness half of the emulated modular
arithmetic (`EmuArith.Complete`), and that the step circuit is satisfiable (`hstepc`).
-/

namespace Sonobe
namespace Gadget

open Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModFC {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]
variable (W1 : WeierstrassCurve (ZMod p2)) [Short W1] [W1.IsElliptic]
  (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G1 : ZMod p2 × ZMod p2) (G2 : ZMod p1 × ZMod p1)
  (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)
  [Module (ZMod p1) W1.toAffine.Point] [Module (ZMod p2) W2.toAffine.Point]

theorem ivc_complete_of_circuits
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254)
    (T : Setup (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    -- identification of the abstract model with the concrete hashes and wiring
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hch2a : T.ch2an = ch2anC W2 sp dT) (hch2b : T.ch2bn = ch2bnC W2 sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstepc : ∀ z, StepRel z (T.step z))
    (hsmul1 : ∀ (n : ℕ) (P : W1.toAffine.Point), (n : ZMod p1) • P = n • P)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    -- the two circuits and the trusted R1CS synthesis (completeness direction)
    (EAc : (EmuArith.concrete hp hp2 hbits).Complete)
    (hcompA : ∀ (x : Fin 1 → ZMod p1) (ω : AugVars p1 sN),
      AugRel W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel ω (x 0) → ∃ w, T.k1.r1cs.Sat x w)
    (circC : Circuit (ZMod p2) 7 T.nw2 (CFWit (ZMod p2))) (hcompC : circC.Compiles T.k2.r1cs)
    (hrelC : ∀ x ω, circC.rel x ω ↔ CFRel W1 128 G1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    -- curve and field facts
    (hb1 : W1.a₆ ≠ 0) (h2a : (2 : ZMod p2) ≠ 0)
    (hnr1 : ∀ e : ZMod p2, e ^ 3 + W1.a₄ * e + W1.a₆ ≠ 0) {r1 : ℕ}
    (hord1 : ∀ P : W1.toAffine.Point, P ≠ 0 → addOrderOf P = r1) (hrn1 : 2 ^ 128 < r1)
    (hG1 : W1.toAffine.Equation G1.1 G1.2)
    (h2b : (2 : ZMod p1) ≠ 0) (hnr2 : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r2 : ℕ}
    (hord2 : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r2) (hrn2 : 2 ^ 128 < r2)
    (hG2 : W2.toAffine.Equation G2.1 G2.2)
    (hp2' : 2 ^ 128 ≤ p2)
    (hp1b : p1 ≤ 2 ^ 254) (hp2b : p2 ≤ 2 ^ 254) (hpm : natVal 254 pm1 = p1 - 1)
    {N : ℕ} (hcast : CastOK (ZMod p1) N) (z0 : Fin sN → ZMod p1) :
    ∀ n ≤ N, ∃ P : Proof T, T.Verify n z0 (T.step^[n] z0) P :=
  ivc_complete T
    (augComplete_of_circuit W1 W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel T hco hhs hch hch2a hch2b hcfx hstepc
      EAc hsmul2 hcompA h2b hnr2 hord2 hrn2 hp hp2 hp2' hp1b hp2b hG2 hpm)
    (cfComplete_of_circuit W1 T hco hcfx hsmul1 hG1 circC hcompC hrelC hb1 h2a hnr1 hord1 hrn1 hp2')
    hcast z0

end Gadget
end Sonobe
