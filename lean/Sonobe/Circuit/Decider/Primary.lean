import Sonobe.Circuit.AugSound
import Sonobe.Circuit.Decider.PedersenOpen
import Sonobe.Circuit.Emulated.R1CSEval

/-!
The decider circuit `CycleFoldBasedIVCDeciderCircuit::generate_constraints`
(ivc/src/compilers/cyclefold/mod.rs), one constraint group per Rust statement:

```
i, z0, zi                = new_input                       -- public
WW, U, u, cf_W, cf_U, π  = new_witness
i ≠ 0
UU = verify_hinted(U, u, π)       -- ρ from the transcript; UU.u = U.u + ρ, UU.x = U.x + ρ u.x,
                                  --   UU.cm_e, UU.cm_w free hints (Tight)
challenges.mark_as_public()                                -- the raw squeezed element
U.cm_e, U.cm_w, u.cm_w, π.cm_t . mark_as_public()          -- packed: 2 elements per coordinate
decide_running(dk1, WW, UU)       -- relaxed R1CS over F1; Pedersen open = UU.cm_e, UU.cm_w public
                                  --   (packed) + the committed variables for the CP-SNARK
decide_running(dk2, cf_W, cf_U)   -- relaxed R1CS over the emulated F2 (`emuR1CS_sound`);
                                  --   Pedersen open: msm + enforce_equal (`OpenRel`)
u.x = [H(i, z0, zi, U, cf_U)]
```
The shared front part (allocations, `u_x` hash, transcript challenge) is `FrontRel`.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModDP {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- Constant Pedersen generators of the secondary key (as projective constants). -/
structure PedConst (p : ℕ) where
  g : ℕ → PP (ZMod p)
  h : PP (ZMod p)

/-- Public inputs: `i, z₀, zᵢ`, the raw squeezed challenge, and the packed coordinates of the
points `U.cm_e, U.cm_w, u.cm_w, π.cm_t, UU.cm_e, UU.cm_w` (two field elements per coordinate). -/
structure DecPub (p1 sN : ℕ) where
  i : ZMod p1
  z0 : Fin sN → ZMod p1
  zi : Fin sN → ZMod p1
  ch : ZMod p1
  pt : Fin 12 → ZMod p1 × ZMod p1

/-- Witnesses of the decider circuit; `v` holds the wires shared with the augmented circuit. -/
structure DecWit (p1 sN m1 nw1 m2 nw2 : ℕ) where
  v : AugVars p1 sN
  qw : Fin 12 → AbsWit p1
  qo : Fin 12 → ZMod p1 × ZMod p1
  we : Fin m1 → ZMod p1
  ww : Fin nw1 → ZMod p1
  cwe : Fin m2 → ℕ → ZMod p1
  cwew : Fin m2 → TightWit p1 8 32
  cww : Fin nw2 → ℕ → ZMod p1
  cwww : Fin nw2 → TightWit p1 8 32
  cre : ℕ → ZMod p1
  crew : TightWit p1 8 32
  crw : ℕ → ZMod p1
  crww : TightWit p1 8 32
  oE : OpenWit p1
  oW : OpenWit p1

/-- Coordinate slot of the `k`-th public coordinate: `U.cm_e, U.cm_w, u.cm_w, π, UU.cm_e,
UU.cm_w` (slots `pa 0 … 11` are `UE, UW, π, In, pe, pw`). -/
def pubIdx : Fin 12 → Fin 12 := ![0, 1, 2, 3, 6, 7, 4, 5, 8, 9, 10, 11]

/-- Scalar limbs as a total function on `ℕ`. -/
def vecN {m : ℕ} (a : Fin m → ℕ → ZMod p1) : ℕ → ℕ → ZMod p1 :=
  fun i => if h : i < m then a ⟨i, h⟩ else fun _ => 0

variable (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  {m1 nw1 m2 nw2 : ℕ}
  (R1 : R1CS (ZMod p1) m1 1 nw1) (R2 : R1CS (ZMod p2) m2 7 nw2)
  (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1)) (pm1 : ℕ → Bool) (G : ZMod p1 × ZMod p1)
  (PE PW : PedConst p1) (pph : ZMod p1)

/-- Constraints of the decider circuit. -/
def DecRel (d : DecWit p1 sN m1 nw1 m2 nw2) (x : DecPub p1 sN) : Prop :=
  -- i ≠ 0
  d.v.i * d.v.invI = 1 ∧ d.v.pp = pph ∧
  -- public inputs
  d.v.i = x.i ∧ d.v.z0 = x.z0 ∧ d.v.zi = x.zi ∧ x.ch = d.v.c ∧
  -- allocations, `u_x`, transcript and challenge
  FrontRel (p2 := p2) W2 sp dS dT pm1 d.v ∧
  -- the packed public points
  (∀ k : Fin 12, EmuAbsRel (d.v.pa (pubIdx k)) (d.qw k) (d.qo k) ∧ x.pt k = d.qo k) ∧
  -- `decide_running(dk1, WW, UU)`: relaxed R1CS over F1 for `UU = U + ρ u`
  R1.RelaxedSat (d.v.Uu + rhoOf d.v.cb) (fun _ => d.v.Ux + rhoOf d.v.cb * d.v.uxIn) d.ww d.we ∧
  -- `decide_running(dk2, cf_W, cf_U)`: allocations, relaxed R1CS, Pedersen openings
  (∀ j, TightRel 8 32 (mlimb p2) (d.cwe j) (d.cwew j)) ∧
  (∀ j, TightRel 8 32 (mlimb p2) (d.cww j) (d.cwww j)) ∧
  TightRel 8 32 (mlimb p2) d.cre d.crew ∧ TightRel 8 32 (mlimb p2) d.crw d.crww ∧
  EmuR1CSC p2 R2 (d.v.sa 0) (fun j => d.v.sa j.succ) d.cww d.cwe ∧
  OpenRel W2 m2 G PE.g PE.h (vecN d.cwe) d.cre d.v.sE d.oE ∧
  OpenRel W2 nw2 G PW.g PW.h (vecN d.cww) d.crw d.v.sW d.oW

omit [Fact p2.Prime] in
theorem vecN_apply {m : ℕ} (a : Fin m → ℕ → ZMod p1) (i : Fin m) : vecN a i = a i := by
  simp [vecN, i.2]

/-- The challenge bits are the low 128 bits of the squeezed element. -/
theorem front_ch_val {v : AugVars p1 sN} (hpm : natVal 254 pm1 = p1 - 1)
    (h : FrontRel (p2 := p2) W2 sp dS dT pm1 v) :
    natVal 128 (fun j => decide (cbN v.cb j = 1)) = v.c.val % 2 ^ 128 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbits⟩ := h
  have hbv := toBits_sound (n := 254) hpm hbits
  have hrho : natVal 128 (bitsOf v.cb) = v.c.val % 2 ^ 128 := by
    rw [hbv]; exact (natVal_mod _ (by norm_num)).symm
  rw [← hrho]
  unfold natVal
  refine sum_congr rfl fun j hj => ?_
  have := mem_range.mp hj
  simp [bitsOf, cbN, show j < 254 by omega]

variable [Module (ZMod p2) W2.toAffine.Point]

/-- **Soundness of the decider circuit** (circuit-level consequences): in terms of the wire
values, everything the decider relation needs. -/
theorem dec_sound
    (hsmul : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    (h2 : (2 : ZMod p1) ≠ 0) (hnr : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r2 : ℕ}
    (hord : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r2) (hrn : 2 ^ 252 < r2)
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (hpm : natVal 254 pm1 = p1 - 1)
    (hgE : ∀ i < m2, (PE.g i).OnCurve W2.a₄ W2.a₆) (hhE : PE.h.OnCurve W2.a₄ W2.a₆)
    (hgW : ∀ i < nw2, (PW.g i).OnCurve W2.a₄ W2.a₆) (hhW : PW.h.OnCurve W2.a₄ W2.a₆)
    {d : DecWit p1 sN m1 nw1 m2 nw2} {x : DecPub p1 sN}
    (h : DecRel W2 R1 R2 sp dS dT pm1 G PE PW pph d x) :
    d.v.i ≠ 0 ∧ x.i = d.v.i ∧ x.z0 = d.v.z0 ∧ x.zi = d.v.zi ∧
    -- the public points are the encodings of the coordinates
    (∀ k, pr (x.pt k) = encE p1 p2 (vE d.v (pubIdx k))) ∧
    -- `u_x`, challenge
    d.v.uxIn = hsC (p2 := p2) W2 sp dS d.v.pp d.v.i d.v.z0 d.v.zi (Uraw (p2 := p2) d.v)
      (SecVar.val (p2 := p2) W2 (secOf d.v.sa d.v.sE d.v.sW)) ∧
    rhoOf d.v.cb = ((ch1nC (p2 := p2) sp dT d.v.pp (Uraw d.v) (uinRaw d.v) (piRaw d.v) : ℕ) : ZMod p1) ∧
    ch1nC (p2 := p2) sp dT d.v.pp (Uraw d.v) (uinRaw d.v) (piRaw d.v) = x.ch.val % 2 ^ 128 ∧
    -- primary relaxed R1CS of `UU`
    R1.RelaxedSat (d.v.Uu + rhoOf d.v.cb) (fun _ => d.v.Ux + rhoOf d.v.cb * d.v.uxIn) d.ww d.we ∧
    -- secondary relaxed R1CS and Pedersen openings
    R2.RelaxedSat (emuV p2 (d.v.sa 0)) (fun j => emuV p2 (d.v.sa j.succ))
      (fun j => emuV p2 (d.cww j)) (fun j => emuV p2 (d.cwe j)) ∧
    (PedersenKey.mk (F := ZMod p2) (fun i : Fin m2 => (PE.g i).pt W2) (PE.h.pt W2)).Opens
      (fun i => emuV p2 (d.cwe i)) (emuV p2 d.cre) (d.v.sE.pt W2) ∧
    (PedersenKey.mk (F := ZMod p2) (fun i : Fin nw2 => (PW.g i).pt W2) (PW.h.pt W2)).Opens
      (fun i => emuV p2 (d.cww i)) (emuV p2 d.crw) (d.v.sW.pt W2) ∧ d.v.pp = pph := by
  obtain ⟨hi, hpp, hxi, hxz, hxzi, hxc, hfront, hpub, hr1, tE, tW, tre, trw, hem, hoE, hoW⟩ := h
  have h32 : 2 ^ 32 ≤ p1 := le_trans (Nat.le_add_right _ _) hp.le
  obtain ⟨cp, cs⟩ := front_canon W2 sp dS dT pm1 hp hp2 hfront
  obtain ⟨hbool, hn128, hrho⟩ := front_rho W2 sp dS dT pm1 hp hp2 hpm hfront
  have hch := front_ch_val W2 sp dS dT pm1 hpm hfront
  have hvalid := hfront
  obtain ⟨-, -, hvE, hvW, -⟩ := hvalid
  refine ⟨?_, hxi.symm, hxz.symm, hxzi.symm, ?_, front_ux W2 sp dS dT pm1 hp hp2 hfront, hrho,
    ?_, hr1, ?_, ?_, ?_, hpp⟩
  · intro h0; rw [h0, zero_mul] at hi; exact zero_ne_one hi
  · intro k
    obtain ⟨ha, hk⟩ := hpub k
    rw [hk]; exact pr_ao_eq_encE h32 (cp _) ha
  · rw [hxc, ← hch, hn128]
  · have cE : ∀ j, Canon p2 (d.cwe j) := fun j => tight_canon hp hp2 (tE j)
    have cW : ∀ j, Canon p2 (d.cww j) := fun j => tight_canon hp hp2 (tW j)
    exact emuR1CS_sound hp hp2 hbits (cs 0) (fun j => cs j.succ) cW cE hem
  · have := open_sound W2 hsmul h2 hnr hord hrn h32 hgE hhE hvE hoE
    simpa [vecN_apply] using this
  · have := open_sound W2 hsmul h2 hnr hord hrn h32 hgW hhW hvW hoW
    simpa [vecN_apply] using this

end Gadget
end Sonobe
