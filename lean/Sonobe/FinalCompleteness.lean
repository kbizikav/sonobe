import Sonobe.Circuit.EmuArithConcrete
import Sonobe.FinalSoundness
import Sonobe.Circuit.AugComplete
import Sonobe.IVC.Completeness
import Sonobe.IVC.Decider

/-!
**IVC completeness from the circuit models**, with the run's hypotheses: for every chain of steps an
honest prover's proof is accepted, its run meets `RunOK` for the decoder of the augmented circuit,
and the decider's relation holds with extraction data meeting `ExtractionOK`. So the hypotheses of
`ivc_sound_of_circuits` and of `IVC.decider_rel_sound` hold together on honest runs.

`IVC.ivc_complete` needs satisfying assignments of the augmented and the CycleFold circuit; they
are derived from the constraint-level models:

* `Gadget.cfComplete_of_circuit` — the honest witness of `verify_point_rlc`;
* `Gadget.augComplete_of_circuit` — the honest witness of the augmented circuit, including the
  Fiat–Shamir derivation of both secondary challenges.

Trusted in addition to the soundness side: the *completeness* direction of the R1CS
synthesis (`constraint model ⇒ R1CS satisfiable`, by a witness that `decode` maps back to the
assignment), the completeness half of the emulated modular arithmetic (`EmuArith.Complete`).
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
  {SW : Type*} (StepRel : (Fin sN → ZMod p1) → SW → (Fin sN → ZMod p1) → Prop)
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
    (hsmul1 : ∀ (n : ℕ) (P : W1.toAffine.Point), (n : ZMod p1) • P = n • P)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    -- the two circuits and the trusted R1CS synthesis (completeness direction)
    (EAc : (EmuArith.concrete hp hp2 hbits).Complete)
    (circA : Circuit (ZMod p1) 1 T.nw1 (AugVars p1 sN))
    (hcompA : ∀ (x : Fin 1 → ZMod p1) (ω : AugVars p1 sN),
      AugRel W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel ω (x 0) →
        ∃ w, T.k1.r1cs.Sat x w ∧ circA.decode w = ω)
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
    ∀ (ws : List SW) (zn : Fin sN → ZMod p1), Chain StepRel z0 ws zn → ws.length ≤ N →
      ∃ (P : Proof T) (ds : List T.StepData), T.Verify ws.length z0 zn P ∧
        (ws ≠ [] → T.RunOK (fun w => augOutOf W2 (circA.decode w)) z0 ws.length zn P ds ∧
          ∃ (D : T.DecOut) (E : T.Extraction), T.DeciderRel ws.length z0 zn D ∧
            T.ExtractionOK (fun w => augOutOf W2 (circA.decode w)) ws.length z0 zn D E) := by
  intro ws zn hc hN
  obtain ⟨P, ds, hV, hrun⟩ := ivc_complete T _
    (augComplete_of_circuit W1 W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel T hco
      hhs hch hch2a hch2b hcfx EAc hsmul2 circA hcompA h2b hnr2 hord2 hrn2 hp hp2 hp2' hp1b hp2b
      hG2 hpm)
    (cfComplete_of_circuit W1 T hco hcfx hsmul1 hG1 circC hcompC hrelC hb1 h2a hnr1 hord1 hrn1 hp2')
    h2b h2a hcast z0 ws zn hc hN
  refine ⟨P, ds, hV, fun hne => ⟨hrun hne, ?_⟩⟩
  have hl : ws.length ≠ 0 := by simpa using hne
  have hP : T.Good ws.length z0 zn P := by simpa [Setup.Verify, hl] using hV
  exact decider_complete T _ h2b hl hP (hrun hne)

end Gadget
end Sonobe
