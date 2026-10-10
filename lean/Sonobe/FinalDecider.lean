import Sonobe.FinalSoundness
import Sonobe.Circuit.Decider.Primary
import Sonobe.EVM.Decider
import Sonobe.IVC.Decider

/-!
**Soundness of the EVM decider verifier, from the circuit models.**

`IVC.decider_sound` assumed `cpSound`, which bundled (a) the knowledge soundness of the CP-SNARK
and (b) that the decider circuit and verifier enforce `DeciderRel`. Here (b) is derived: the decider
circuit is modelled constraint by constraint (`Circuit/Decider`), the contract at the level of
words (`EVM/Decider`), and the only assumption left on the CP-SNARK is
`LegoGroth16.CPKnowledgeSound`.
-/

namespace Sonobe
namespace Gadget

open Finset Sonobe.IVC Sonobe.Nova Sonobe.EVM
open scoped Classical

noncomputable local instance decEqZModFD {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 sN : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-- The public inputs as the list `[i, z₀.., zᵢ.., challenge, (lo, hi)..]` of the circuit. -/
def DecPub.toList (p : DecPub p1 sN) : List (ZMod p1) :=
  [p.i] ++ List.ofFn p.z0 ++ List.ofFn p.zi ++ [p.ch] ++
    (List.ofFn p.pt).flatMap fun q => [q.1, q.2]

/-- The public inputs the contract feeds the verifier, as field elements. -/
def pubOfCd {PW : Type*} (cd : Calldata sN PW) (pts : Fin 6 → ℕ × ℕ) : DecPub p1 sN where
  i := (cd.i : ZMod p1)
  z0 := fun k => (cd.z0 k : ZMod p1)
  zi := fun k => (cd.zi k : ZMod p1)
  ch := (cd.challenge : ZMod p1)
  pt := fun k => ((packLo (coordW pts k) : ZMod p1), (packHi (coordW pts k) : ZMod p1))

theorem flatten_ofFn_singleton {α : Type*} : ∀ {n : ℕ} (f : Fin n → α),
    (List.ofFn fun x => [f x]).flatten = List.ofFn f
  | 0, _ => by simp
  | n + 1, f => by
    simp [List.ofFn_succ, flatten_ofFn_singleton (fun i : Fin n => f i.succ)]

theorem xList_map {PW : Type*} (cd : Calldata sN PW) (pts : Fin 6 → ℕ × ℕ) :
    (xList cd pts).map (fun w => (w : ZMod p1)) = (pubOfCd cd pts : DecPub p1 sN).toList := by
  simp [xList, DecPub.toList, pubOfCd, List.map_flatten, List.flatMap, Function.comp_def, flatten_ofFn_singleton]

theorem encE_inj (hp1 : 2 ^ 253 < p1) (hp2 : p2 ≤ 2 ^ 254) {v v' : ZMod p2}
    (h : encE p1 p2 v = encE p1 p2 v') : v = v' := by
  simp only [encE, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  have lt1 : ∀ a : ℕ, a < 2 ^ 253 → a < p1 := fun a ha => lt_trans ha hp1
  have a1 : v.val % 2 ^ 253 = v'.val % 2 ^ 253 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ p1).mp h1
    rwa [Nat.mod_eq_of_lt (lt1 _ (Nat.mod_lt _ (by positivity))),
      Nat.mod_eq_of_lt (lt1 _ (Nat.mod_lt _ (by positivity)))] at this
  have hv : ∀ w : ZMod p2, w.val / 2 ^ 253 < 2 := fun w => by
    have := ZMod.val_lt w
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have a2 : v.val / 2 ^ 253 = v'.val / 2 ^ 253 := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ p1).mp h2
    have h2p : 2 < p1 := lt_trans (by norm_num : 2 < 2 ^ 253) hp1
    rwa [Nat.mod_eq_of_lt (lt_trans (hv v) h2p), Nat.mod_eq_of_lt (lt_trans (hv v') h2p)] at this
  apply ZMod.val_injective
  rw [← Nat.mod_add_div v.val (2 ^ 253), ← Nat.mod_add_div v'.val (2 ^ 253), a1, a2]

theorem coords_of_decode {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve (ZMod q)) [Short W]
    [W.IsElliptic] {a : ℕ × ℕ} {P : W.toAffine.Point} (h : decodeG1 W a = some P) :
    coordsOf W P = ((a.1 : ZMod q), (a.2 : ZMod q)) := by
  obtain ⟨h1, h2, h3⟩ := decode_some W h
  have e1 : (coordsOf W P).1.val = a.1 := by rw [← h3]; rfl
  have e2 : (coordsOf W P).2.val = a.2 := by rw [← h3]; rfl
  ext
  · simp only; rw [← e1, ZMod.natCast_zmod_val]
  · simp only; rw [← e2, ZMod.natCast_zmod_val]

section Final

variable (W1 : WeierstrassCurve (ZMod p2)) [Short W1] [W1.IsElliptic]
  (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]
  (sp : SpongeCfg (ZMod p1)) (dS dT : List (ZMod p1))
  (pm1 : ℕ → Bool) (G1 : ZMod p2 × ZMod p2) (G2 : ZMod p1 × ZMod p1)
  (StepRel : (Fin sN → ZMod p1) → (Fin sN → ZMod p1) → Prop)
  [Module (ZMod p1) W1.toAffine.Point] [Module (ZMod p2) W2.toAffine.Point]

theorem evm_decider_sound
    {PWd G₂ G_T : Type*} [AddCommGroup G₂] [Module (ZMod p1) G₂] [AddCommGroup G_T]
    [Module (ZMod p1) G_T]
    (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254)
    (T : Setup (ZMod p1) W1.toAffine.Point (ZMod p2) W2.toAffine.Point (Fin sN → ZMod p1)
      (ZMod p2 × ZMod p2) 7)
    -- identification of the abstract model with the concrete hash, challenge and wiring
    (hco : T.coords = coordsOf W1) (hhs : T.hs = hsC W2 sp dS) (hch : T.ch1n = ch1nC sp dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    (hstep : ∀ z z', StepRel z z' → z' = T.step z)
    (hsmul1 : ∀ (n : ℕ) (P : W1.toAffine.Point), (n : ZMod p1) • P = n • P)
    (hsmul2 : ∀ (n : ℕ) (P : W2.toAffine.Point), (n : ZMod p2) • P = n • P)
    -- the augmented and the CycleFold circuit
    (circA : Circuit (ZMod p1) 1 T.nw1 (AugVars p1 sN))
    (hsatA : ∀ x w, T.k1.r1cs.Sat x w → circA.rel x (circA.decode w))
    (hrelA : ∀ x ω, circA.rel x ω → AugRel W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel ω (x 0))
    (circC : Circuit (ZMod p2) 7 T.nw2 (CFWit (ZMod p2))) (hcompC : circC.Compiles T.k2.r1cs)
    (hrelC : ∀ x ω, circC.rel x ω ↔ CFRel W1 128 G1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    -- the decider circuit, its synthesis and the emulated R1CS assumption
    (PEc PWc : PedConst p1) (pph : ZMod p1) (hpph : T.pph = pph)
    (hkE : T.k2.ckE = PedersenKey.mk (F := ZMod p2) (fun i : Fin T.m2 => (PEc.g i).pt W2)
      (PEc.h.pt W2))
    (hkW : T.k2.ckW = PedersenKey.mk (F := ZMod p2) (fun i : Fin T.nw2 => (PWc.g i).pt W2)
      (PWc.h.pt W2))
    (hgE : ∀ i < T.m2, (PEc.g i).OnCurve W2.a₄ W2.a₆) (hhE : PEc.h.OnCurve W2.a₄ W2.a₆)
    (hgW : ∀ i < T.nw2, (PWc.g i).OnCurve W2.a₄ W2.a₆) (hhW : PWc.h.OnCurve W2.a₄ W2.a₆)
    {mD nwD : ℕ}
    (circD : Circuit (ZMod p1) (2 * sN + 26) nwD (DecWit p1 sN T.m1 T.nw1 T.m2 T.nw2))
    (RD : R1CS (ZMod p1) mD (2 * sN + 26) nwD)
    (hsatD : ∀ x w, RD.Sat x w → circD.rel x (circD.decode w))
    (hrelD : ∀ (p : DecPub p1 sN) ω, circD.rel (vecOfList p.toList (2 * sN + 26)) ω →
      DecRel W2 T.k1.r1cs T.k2.r1cs sp dS dT pm1 G2 PEc PWc pph ω p)
    -- the CP-SNARK and its knowledge soundness (the one cryptographic assumption on it)
    (e : W1.toAffine.Point →ₗ[ZMod p1] G₂ →ₗ[ZMod p1] G_T)
    (vk : LegoGroth16.VK W1.toAffine.Point G₂ (2 * sN + 26) 2)
    (decodeProof : PWd → Option (LegoGroth16.Proof W1.toAffine.Point G₂))
    (hcp : LegoGroth16.CPKnowledgeSound e vk RD
      (fun w => ((circD.decode w).we, (circD.decode w).ww)) T.k1.ckE T.k1.ckW)
    -- curve and field facts
    (hb1 : W1.a₆ ≠ 0) (h2a : (2 : ZMod p2) ≠ 0)
    (hnr1 : ∀ e : ZMod p2, e ^ 3 + W1.a₄ * e + W1.a₆ ≠ 0) {r1 : ℕ}
    (hord1 : ∀ P : W1.toAffine.Point, P ≠ 0 → addOrderOf P = r1) (hrn1 : 2 ^ 128 < r1)
    (hG1 : W1.toAffine.Equation G1.1 G1.2)
    (h2b : (2 : ZMod p1) ≠ 0) (hnr2 : ∀ e : ZMod p1, e ^ 3 + W2.a₄ * e + W2.a₆ ≠ 0) {r2 : ℕ}
    (hord2 : ∀ P : W2.toAffine.Point, P ≠ 0 → addOrderOf P = r2) (hrn2 : 2 ^ 252 < r2)
    (hG2 : W2.toAffine.Equation G2.1 G2.2)
    (hp2' : 2 ^ 128 ≤ p2)
    (hp1b : 2 ^ 253 < p1) (hp2b : p2 ≤ 2 ^ 254)
    (hpm : natVal 254 pm1 = p1 - 1)
    -- cryptographic assumptions
    (hH : T.HsInj) (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK (ZMod p1) N)
    -- the call
    (cd : Calldata sN PWd) (hn : cd.i ≤ N) (hacc : DeciderAccepts W1 e vk decodeProof cd) :
    (fun k => (cd.zi k : ZMod p1)) = T.step^[cd.i] (fun k => (cd.z0 k : ZMod p1)) := by
  have hrn2' : 2 ^ 128 < r2 :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hrn2
  have hA := augSound_of_circuit W1 W2 (EmuArith.concrete hp hp2 hbits) sp dS dT pm1 G2 StepRel T hco hhs hch hcfx hstep hsmul2
    circA hsatA hrelA h2b hnr2 hord2 hrn2' hp hp2 hp2' hG2 hpm
  have hC := cfSound_of_circuit W1 T hco hcfx hsmul1 hG1 circC hcompC hrelC hb1 h2a hnr1 hord1
    hrn1 hp2'
  rcases hacc with ⟨hi0, hz⟩ | ⟨hi0, ce, cw, hce, hcw, hvp⟩
  · funext k; rw [hi0, Function.iterate_zero, id, hz]
  obtain ⟨hlen, hlt, cG, π, hdec, hdecP, hacc'⟩ := hvp
  set pts := ptsOf cd ce cw with hpts
  rw [xList_map cd pts] at hacc'
  obtain ⟨w, o, hsat, hc0, hc1⟩ := hcp _ cG π hacc'
  have hrel := hrelD (pubOfCd cd pts) (circD.decode w) (hsatD _ w hsat)
  set d := circD.decode w with hd
  obtain ⟨hnz, hxi, hxz, hxzi, hpt, hux, hrho, hchv, hR1, hR2, hOE, hOW, hpp⟩ :=
    dec_sound W2 T.k1.r1cs T.k2.r1cs sp dS dT pm1 G2 PEc PWc pph hsmul2 h2b hnr2 hord2 hrn2
      hp hp2 hbits hpm hgE hhE hgW hhW hrel
  obtain ⟨PUE, Pπ, hPUE, hPπ, hce'⟩ := foldC_spec W1 hb1 hce
  obtain ⟨PUW, Pu, hPUW, hPu, hcw'⟩ := foldC_spec W1 hb1 hcw
  have d0 := hdec 0
  have d1 := hdec 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at d0 d1
  -- canonical words
  have l1 := decode_some W1 hPUE
  have l2 := decode_some W1 hPπ
  have l3 := decode_some W1 hPUW
  have l4 := decode_some W1 hPu
  have l5 := decode_some W1 d0
  have l6 := decode_some W1 d1
  have hwlt : ∀ k : Fin 12, coordW pts k < p2 := by
    intro k
    fin_cases k <;> simp [coordW, hpts, ptsOf] <;> omega
  have key : ∀ k, pr ((pubOfCd cd pts : DecPub p1 sN).pt k) =
      encE p1 p2 ((coordW pts k : ℕ) : ZMod p2) := by
    intro k
    simp [pubOfCd, pr, encE, packLo, packHi, ZMod.val_natCast_of_lt (hwlt k)]
  have hslot : ∀ k, vE d.v (pubIdx k) = ((coordW pts k : ℕ) : ZMod p2) := by
    intro k
    apply encE_inj hp1b hp2b
    rw [← hpt k, key k]
  have e0 : vE d.v 0 = ((cd.uCmE.1 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 0
  have e1 : vE d.v 1 = ((cd.uCmE.2 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 1
  have e2 : vE d.v 2 = ((cd.uCmW.1 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 2
  have e3 : vE d.v 3 = ((cd.uCmW.2 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 3
  have e6 : vE d.v 6 = ((cd.ucmW.1 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 4
  have e7 : vE d.v 7 = ((cd.ucmW.2 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 5
  have e4 : vE d.v 4 = ((cd.cmT.1 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 6
  have e5 : vE d.v 5 = ((cd.cmT.2 : ℕ) : ZMod p2) := by
    simpa [pubIdx, coordW, hpts, ptsOf] using hslot 7
  -- the genuine group elements behind the calldata points
  have cE := coords_of_decode W1 hPUE
  have cW := coords_of_decode W1 hPUW
  have cI := coords_of_decode W1 hPu
  have cT := coords_of_decode W1 hPπ
  set U : RunningInstance (ZMod p1) W1.toAffine.Point 1 := ⟨PUE, d.v.Uu, PUW, fun _ => d.v.Ux⟩
    with hU
  set u : IncomingInstance W1.toAffine.Point (ZMod p1) 1 := ⟨Pu, fun _ => d.v.uxIn⟩ with hu
  have hrawU : T.rawOf U = Uraw d.v := by
    simp [Setup.rawOf, hU, hco, cE, cW, Uraw, e0, e1, e2, e3]
  have hrawI : T.rawOfI u = uinRaw d.v := by
    simp [Setup.rawOfI, hu, hco, cI, uinRaw, e6, e7]
  have hcoP : T.coords Pπ = piRaw d.v := by simp [hco, cT, piRaw, e4, e5]
  have hpp' : d.v.pp = T.pph := hpp.trans hpph.symm
  have hρ : T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords Pπ) = rhoOf d.v.cb := by
    rw [hrawU, hrawI, hcoP, Setup.ch1, hch, ← hpp']; exact hrho.symm
  -- the challenge of the verifier
  have hchlt : cd.challenge < p1 := hlt _ (by simp [xList])
  have hchval : (pubOfCd cd pts : DecPub p1 sN).ch.val = cd.challenge :=
    ZMod.val_natCast_of_lt hchlt
  have hρV : ch1nC (p2 := p2) sp dT d.v.pp (Uraw d.v) (uinRaw d.v) (piRaw d.v) =
      cd.challenge % 2 ^ 128 := by rw [hchv, hchval]
  have hρcast : rhoOf d.v.cb = (((cd.challenge % 2 ^ 128 : ℕ)) : ZMod p1) := by rw [hrho, hρV]
  -- the folded commitments
  have hc0' : cG 0 = PUE + (cd.challenge % 2 ^ 128) • Pπ := by
    rw [hce', decode_encode W1 hb1] at d0
    exact (Option.some.inj d0).symm
  have hc1' : cG 1 = PUW + (cd.challenge % 2 ^ 128) • Pu := by
    rw [hcw', decode_encode W1 hb1] at d1
    exact (Option.some.inj d1).symm
  have hsm : ∀ P : W1.toAffine.Point, rhoOf d.v.cb • P = (cd.challenge % 2 ^ 128) • P := by
    intro P; rw [hρcast]; exact hsmul1 _ P
  set WW : RunningWitness (ZMod p1) T.m1 T.nw1 := ⟨d.we, o 0, d.ww, o 1⟩ with hWW
  have hfold : T.fold1 U u Pπ = foldInstance (rhoOf d.v.cb) Pπ U u := by
    unfold Setup.fold1; rw [hρ]
  have hrun : T.k1.Running (T.fold1 U u Pπ) WW := by
    rw [hfold]
    refine ⟨?_, ?_, ?_⟩
    · simpa [R1CS.RelaxedSat, foldInstance, hU, hu, hWW] using hR1
    · show T.k1.ckE.commit d.we (o 0) = _
      rw [← show (circD.decode w).we = d.we from rfl, ← hc0]
      simp only [foldInstance, hU, hsm, hc0']
    · show T.k1.ckW.commit d.ww (o 1) = _
      rw [← show (circD.decode w).ww = d.ww from rfl, ← hc1]
      simp only [foldInstance, hU, hu, hsm, hc1']
  set cfU := SecVar.val (p2 := p2) W2 (secOf d.v.sa d.v.sE d.v.sW) with hcfU
  set cfW : RunningWitness (ZMod p2) T.m2 T.nw2 :=
    ⟨fun j => emuV p2 (d.cwe j), emuV p2 d.cre, fun j => emuV p2 (d.cww j), emuV p2 d.crw⟩
    with hcfW
  have hcf : T.k2.Running cfU cfW := by
    refine ⟨hR2, ?_, ?_⟩
    · rw [hkE]; exact hOE
    · rw [hkW]; exact hOW
  have hi' : d.v.i = ((cd.i : ℕ) : ZMod p1) := hxi.symm
  have hz0' : d.v.z0 = fun k => (cd.z0 k : ZMod p1) := hxz.symm
  have hzi' : d.v.zi = fun k => (cd.zi k : ZMod p1) := hxzi.symm
  have hux' : u.x = fun _ => T.hs T.pph ((cd.i : ℕ) : ZMod p1) (fun k => (cd.z0 k : ZMod p1))
      (fun k => (cd.zi k : ZMod p1)) (T.rawOf U) cfU := by
    funext _
    show d.v.uxIn = _
    rw [hux, hhs, hrawU, hpp', hi', hz0', hzi']
  exact decider_rel_sound T hA hC hH hE1 hW1 hE2 hW2 f1 f2 hcast hn
    ⟨hi0, U, u, Pπ, WW, cfU, cfW, hux', hrun, hcf⟩

end Final

end Gadget
end Sonobe
