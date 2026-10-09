import Sonobe.Circuit.AugSound
import Sonobe.Circuit.CFBridge

/-!
**IVC soundness with the circuit assumptions derived.**

`IVC2.ivc_sound` assumed `AugSound` and `CFSound`, statements about satisfying assignments of the
augmented and the CycleFold circuit. Here both are *derived* from constraint-level models of the
Rust gadgets:

* `Gadget.cfSound_of_circuit` — CycleFold circuit (bit decomposition, `to_affine`, the
  double-and-add chain with incomplete formulas, the Renes–Costello–Batina complete addition);
* `Gadget.augSound_of_circuit` — augmented circuit (canonical `Tight` limbs, emulated absorb,
  duplex sponge, canonical `to_bits_le`, primary/secondary fold verifiers, base-case selects).

What remains assumed is listed in the hypotheses of the theorem.
-/

namespace Sonobe
namespace Gadget

open Sonobe.IVC2 Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModFin {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]
variable (W1 : WeierstrassCurve (ZMod p2)) [Short W1] [W1.IsElliptic]
  (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (EA : EmuArith p1 p2) (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G1 : ZMod p2 × ZMod p2) (G2 : ZMod p1 × ZMod p1)
  (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)
  [Module (ZMod p1) W1.toAffine.Point] [Module (ZMod p2) W2.toAffine.Point]

theorem ivc_sound_of_circuits
    (T : Setup2 (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    -- identification of the abstract model with the concrete hash, challenge and wiring
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstep : ∀ z z', StepRel z z' → z' = T.step z)
    (hsmul1 : ∀ (n : ℕ) (P : W1.toAffine.Point), (n : ZMod p1) • P = n • P)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    -- the two circuits and the trusted R1CS synthesis
    (circA : Circuit (ZMod p1) 1 T.nw1 (AugVars p1 sN))
    (hsatA : ∀ x w, T.k1.r1cs.Sat x w → circA.rel x (circA.decode w))
    (hrelA : ∀ x ω, circA.rel x ω → AugRel W2 EA sp dS dT pm1 G2 StepRel ω (x 0))
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
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8)) (hp2' : 2 ^ 128 ≤ p2)
    (hpm : natVal 254 pm1 = p1 - 1)
    -- cryptographic assumptions
    (hH : T.HsInj) (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK (ZMod p1) N) (z0 : Fin sN → ZMod p1) :
    ∀ n, n + 1 ≤ N → ∀ (zn : Fin sN → ZMod p1) (P : Proof2 T), T.Good (n + 1) z0 zn P →
      zn = T.step^[n + 1] z0 :=
  ivc_sound T
    (augSound_of_circuit W1 W2 EA sp dS dT pm1 G2 StepRel T hco hhs hch hcfx hstep hsmul2 circA
      hsatA hrelA h2b hnr2 hord2 hrn2 hp hp2 hp2' hG2 hpm)
    (cfSound_of_circuit W1 T hco hcfx hsmul1 hG1 circC hcompC hrelC hb1 h2a hnr1 hord1 hrn1 hp2')
    hH hE1 hW1 hE2 hW2 f1 f2 hcast z0

end Gadget
end Sonobe
