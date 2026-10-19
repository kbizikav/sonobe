import Sonobe.FinalDecider
import Sonobe.FinalCompleteness
import Sonobe.Transcript.Poseidon
import Sonobe.Primes

/-!
**The deployment.** BN254 is the primary curve and Grumpkin the secondary; the transcript and the
state hash are arkworks' `PoseidonSponge` with circomlib's `Poseidon(4)` (`Poseidon.circom5`,
zERC20's `POSEIDON4`); the hash and the transcript are separated by the domains `"sponge"` and
`"transcript"` (ivc/src/compilers/cyclefold/circuits.rs:112-114).

* `evm_decider_sound_deployed` — `evm_decider_sound` for these parameters;
* `ivc_complete_deployed` — `ivc_complete_of_circuits` for them: honest runs are accepted and meet
  the run hypotheses.

The field orders are prime by Pratt certificates (`Primes`) and the numeric facts are proved.
Hypotheses that remain: the scalar actions on the curve groups and their prime orders, and the
circuit models, keys, CP-SNARK and run hypotheses of the general theorems.
-/

namespace Sonobe
namespace Deployment

open Sonobe.IVC Sonobe.Nova Sonobe.Gadget Sonobe.EVM

noncomputable local instance decEqZModDep {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

/-- BN254's scalar field order (`Fr`), the base field of Grumpkin. -/
def r : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254's base field order (`Fq`), the scalar field of Grumpkin. -/
def q : ℕ := 21888242871839275222246405745257275088696311157297823662689037894645226208583

theorem natCast_ne_zero {n : ℕ} [NeZero n] {m : ℕ} (h0 : m ≠ 0) (hm : m < n) :
    (m : ZMod n) ≠ 0 := by
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm, ZMod.val_zero] at this
  exact h0 this

theorem natVal_testBit (m : ℕ) : ∀ n, natVal n m.testBit = m % 2 ^ n
  | 0 => by simp [natVal, Nat.mod_one]
  | n + 1 => by
    rw [natVal, Finset.sum_range_succ, ← natVal, natVal_testBit m n, Nat.mod_pow_succ,
      Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ n) with h | h <;> simp [h]

/-- The bits of `r - 1`, against which `to_bits_le` checks a field element. -/
def rm1 : ℕ → Bool := (r - 1).testBit

theorem rm1_val : natVal 254 rm1 = r - 1 := by
  rw [rm1, natVal_testBit, Nat.mod_eq_of_lt (by norm_num [r])]

theorem hp : 2 ^ 32 + 2 ^ 33 < r := by norm_num [r]

theorem hq : q < 2 ^ (32 * 8) := by norm_num [q]

theorem hbits : bitsLen ((q : ℤ) - 1) = 254 := by
  have hq0 : 0 < q := by norm_num [q]
  have e : ((q : ℤ) - 1).natAbs = q - 1 := by omega
  rw [bitsLen, e]
  exact le_antisymm (Nat.size_le.mpr (by norm_num [q])) (Nat.lt_size.mpr (by norm_num [q]))

instance : Fact r.Prime := ⟨Primes.prime_r⟩

instance : Fact q.Prime := ⟨Primes.prime_q⟩

/-! ### The curves -/

/-- BN254, `y² = x³ + 3` over `Fq` (`ark_bn254::g1`). -/
def bn254 : WeierstrassCurve (ZMod q) := ⟨0, 0, 0, 0, 3⟩

/-- Grumpkin, `y² = x³ - 17` over `Fr` (`ark_grumpkin`). -/
def grumpkin : WeierstrassCurve (ZMod r) := ⟨0, 0, 0, 0, -17⟩

instance : Short bn254 := ⟨rfl, rfl, rfl⟩

instance : Short grumpkin := ⟨rfl, rfl, rfl⟩

instance : bn254.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  have h : bn254.Δ = -((3888 : ℕ) : ZMod q) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, bn254]
    push_cast; ring
  rw [h, neg_ne_zero]
  exact natCast_ne_zero (by norm_num) (by norm_num [q])

instance : grumpkin.IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  have h : grumpkin.Δ = -((124848 : ℕ) : ZMod r) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, grumpkin]
    push_cast; ring
  rw [h, neg_ne_zero]
  exact natCast_ne_zero (by norm_num) (by norm_num [r])

/-- BN254's generator `(1, 2)` (`G1_GENERATOR_X/Y`), substituted for an infinite base by
`scalar_mul_le` in the CycleFold circuit. -/
def g1 : ZMod q × ZMod q := (1, 2)

/-- Grumpkin's generator `(1, √-16)` (`G_GENERATOR_X/Y`), substituted for an infinite base by
`scalar_mul_le` in the augmented circuit. -/
def g2 : ZMod r × ZMod r := (1, 17631683881184975370165255887551781615748388533673675138860)

theorem g1_on : bn254.toAffine.Equation g1.1 g1.2 := by
  rw [equation_short]
  simp only [g1, bn254]
  norm_num

theorem g2_on : grumpkin.toAffine.Equation g2.1 g2.2 := by
  rw [equation_short]
  simp only [g2, grumpkin]
  have h : ((17631683881184975370165255887551781615748388533673675138860 ^ 2 + 16 : ℕ) : ZMod r) =
      0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨14202888660651774624073442957165127430048, by norm_num [r]⟩
  push_cast at h
  linear_combination h

/-! ### The transcript -/

/-- `Transcript::separate_domain(d)`: the `u64` length and the bytes of `d`, little-endian, in limbs
of `(MODULUS_BIT_SIZE - 1) / 8 = 31` bytes; one limb for a domain of up to 23 bytes. -/
def domain (d : String) : List (ZMod r) :=
  [((d.toUTF8.size + 2 ^ 64 * d.toUTF8.toList.foldr (fun b acc => b.toNat + 256 * acc) 0 : ℕ) :
    ZMod r)]

/-- The domain of the state hash. -/
def dS : List (ZMod r) := domain "sponge"

/-- The domain of the Fiat–Shamir transcript. -/
def dT : List (ZMod r) := domain "transcript"

/-- The sponge: circomlib's `Poseidon(4)` permutation, rate 4, capacity 1. -/
def sponge : SpongeCfg (ZMod r) := (Poseidon.circom5 : Poseidon.Params (ZMod r) 5).cfg

/-- The emulated arithmetic of `Fq` over `Fr`, derived from its constraints. -/
noncomputable def emu : EmuArith r q := EmuArith.concrete hp hq hbits

theorem castOK_of_lt {N : ℕ} (hN : N < r) : CastOK (ZMod r) N := by
  intro n hn h
  by_contra h0
  exact natCast_ne_zero h0 (by omega) h

/-! ### The theorems -/

variable [Module (ZMod r) bn254.toAffine.Point] [Module (ZMod q) grumpkin.toAffine.Point]

/-- **Soundness of the deployed EVM decider verifier.** If the contract accepts the call `cd`, and
the run meets its hypotheses — the CP-SNARK's extractor outputs a valid witness on the call (`hcp`),
and every rewinding of the run is accepting and breaks no binding, with no hash collision (`hE`) —
then `cd.i` assignments of the step circuit chain `z₀` to `zᵢ`. -/
theorem evm_decider_sound_deployed
    {sN : ℕ} {SW : Type*} (StepRel : (Fin sN → ZMod r) → SW → (Fin sN → ZMod r) → Prop)
    {PWd G₂ G_T : Type*} [AddCommGroup G₂] [Module (ZMod r) G₂] [AddCommGroup G_T]
    [Module (ZMod r) G_T]
    (T : Setup (ZMod r) bn254.toAffine.Point (ZMod q) grumpkin.toAffine.Point (Fin sN → ZMod r)
      (ZMod q × ZMod q) 7)
    -- identification of the abstract model with the concrete hash, challenge and wiring
    (hco : T.coords = coordsOf bn254) (hhs : T.hs = hsC grumpkin sponge dS)
    (hch : T.ch1n = ch1nC sponge dT) (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    -- the augmented and the CycleFold circuit
    (circA : Circuit (ZMod r) 1 T.nw1 (AugVars r sN))
    (hsatA : ∀ x w, T.k1.r1cs.Sat x w → circA.rel x (circA.decode w))
    (hrelA : ∀ x ω, circA.rel x ω → AugRel grumpkin emu sponge dS dT rm1 g2 StepRel ω (x 0))
    (circC : Circuit (ZMod q) 7 T.nw2 (CFWit (ZMod q))) (hcompC : circC.Compiles T.k2.r1cs)
    (hrelC : ∀ x ω, circC.rel x ω ↔ CFRel bn254 128 g1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    -- the decider circuit and its synthesis
    (PEc PWc : PedConst r) (pph : ZMod r) (hpph : T.pph = pph)
    (hkE : T.k2.ckE = PedersenKey.mk (F := ZMod q) (fun i : Fin T.m2 => (PEc.g i).pt grumpkin)
      (PEc.h.pt grumpkin))
    (hkW : T.k2.ckW = PedersenKey.mk (F := ZMod q) (fun i : Fin T.nw2 => (PWc.g i).pt grumpkin)
      (PWc.h.pt grumpkin))
    (hgE : ∀ i < T.m2, (PEc.g i).OnCurve grumpkin.a₄ grumpkin.a₆)
    (hhE : PEc.h.OnCurve grumpkin.a₄ grumpkin.a₆)
    (hgW : ∀ i < T.nw2, (PWc.g i).OnCurve grumpkin.a₄ grumpkin.a₆)
    (hhW : PWc.h.OnCurve grumpkin.a₄ grumpkin.a₆)
    {mD nwD : ℕ}
    (circD : Circuit (ZMod r) (2 * sN + 26) nwD (DecWit r sN T.m1 T.nw1 T.m2 T.nw2))
    (RD : R1CS (ZMod r) mD (2 * sN + 26) nwD)
    (hsatD : ∀ x w, RD.Sat x w → circD.rel x (circD.decode w))
    (hrelD : ∀ (p : DecPub r sN) ω, circD.rel (vecOfList p.toList (2 * sN + 26)) ω →
      DecRel grumpkin T.k1.r1cs T.k2.r1cs sponge dS dT rm1 g2 PEc PWc pph ω p)
    -- the CP-SNARK
    (e : bn254.toAffine.Point →ₗ[ZMod r] G₂ →ₗ[ZMod r] G_T)
    (vk : LegoGroth16.VK bn254.toAffine.Point G₂ (2 * sN + 26) 2)
    (decodeProof : PWd → Option (LegoGroth16.Proof bn254.toAffine.Point G₂))
    -- the curve groups have prime order
    (hord1 : ∀ P : bn254.toAffine.Point, P ≠ 0 → addOrderOf P = r)
    (hord2 : ∀ P : grumpkin.toAffine.Point, P ≠ 0 → addOrderOf P = q)
    -- the call
    (cd : Calldata sN PWd) (hacc : DeciderAccepts bn254 e vk decodeProof cd)
    -- the run's hypotheses: the witness the CP-SNARK's extractor outputs on the call, and the
    -- rewindings of every fold; they are accepting, no binding break, no collision
    (wD : Fin nwD → ZMod r) (o : Fin 2 → ZMod r)
    (hcp : ∀ cG π, (∀ j, decodeG1 bn254 (![ceOf bn254 cd, cwOf bn254 cd] j) = some (cG j)) →
      decodeProof cd.proof = some π →
      LegoGroth16.ExtractsAt e vk RD (fun w => ((circD.decode w).we, (circD.decode w).ww))
        T.k1.ckE T.k1.ckW (xOf bn254 cd (2 * sN + 26)) cG π wD o)
    (E : T.Extraction)
    (hE : T.ExtractionOK (fun w => augOutOf grumpkin (circA.decode w)) cd.i
      (fun k => (cd.z0 k : ZMod r)) (fun k => (cd.zi k : ZMod r))
      (decOutOf bn254 grumpkin T cd (circD.decode wD) o) E) :
    ∃ ws : List SW, ws.length = cd.i ∧
      Chain StepRel (fun k => (cd.z0 k : ZMod r)) ws (fun k => (cd.zi k : ZMod r)) := by
  have hi : cd.i < r := by
    rcases hacc with ⟨hi0, -⟩ | ⟨-, ce, cw, -, -, hvp⟩
    · rw [hi0]; norm_num [r]
    · exact hvp.2.1 cd.i (by simp [xList])
  have h2q : (2 : ZMod q) ≠ 0 := by exact_mod_cast natCast_ne_zero (n := q) (by norm_num) (by norm_num [q])
  have h2r : (2 : ZMod r) ≠ 0 := by exact_mod_cast natCast_ne_zero (n := r) (by norm_num) (by norm_num [r])
  have h3 : bn254.a₆ ≠ 0 := by
    show (3 : ZMod q) ≠ 0
    exact_mod_cast natCast_ne_zero (n := q) (by norm_num) (by norm_num [q])
  exact evm_decider_sound bn254 grumpkin sponge dS dT rm1 g1 g2 StepRel hp hq hbits T hco hhs hch
    hcfx circA hsatA hrelA circC hcompC hrelC PEc PWc pph hpph hkE hkW hgE hhE hgW hhW
    circD RD hsatD hrelD e vk decodeProof h3 h2q hord1 (by norm_num [r]) h2r hord2
    (by norm_num [q]) (by norm_num [q]) (by norm_num [r]) (by norm_num [q]) rm1_val
    (castOK_of_lt hi) cd le_rfl hacc wD o hcp E hE

/-- **Completeness of the deployment, with the run's hypotheses**: for every chain of `n < r` steps
an honest prover's proof is accepted, its run meets `RunOK`, and the decider's relation holds with
extraction data meeting `ExtractionOK`. -/
theorem ivc_complete_deployed
    {sN : ℕ} {SW : Type*} (StepRel : (Fin sN → ZMod r) → SW → (Fin sN → ZMod r) → Prop)
    (T : Setup (ZMod r) bn254.toAffine.Point (ZMod q) grumpkin.toAffine.Point (Fin sN → ZMod r)
      (ZMod q × ZMod q) 7)
    -- identification of the abstract model with the concrete hashes and wiring
    (hco : T.coords = coordsOf bn254) (hhs : T.hs = hsC grumpkin sponge dS)
    (hch : T.ch1n = ch1nC sponge dT) (hch2a : T.ch2an = ch2anC grumpkin sponge dT)
    (hch2b : T.ch2bn = ch2bnC grumpkin sponge dT)
    (hcfx : ∀ n c0 c1 c2, T.cfX n c0 c1 c2 = cfVec n c0 c1 c2)
    -- the two circuits and the trusted R1CS synthesis (completeness direction)
    (EAc : emu.Complete)
    (circA : Circuit (ZMod r) 1 T.nw1 (AugVars r sN))
    (hcompA : ∀ (x : Fin 1 → ZMod r) (ω : AugVars r sN),
      AugRel grumpkin emu sponge dS dT rm1 g2 StepRel ω (x 0) →
        ∃ w, T.k1.r1cs.Sat x w ∧ circA.decode w = ω)
    (circC : Circuit (ZMod q) 7 T.nw2 (CFWit (ZMod q))) (hcompC : circC.Compiles T.k2.r1cs)
    (hrelC : ∀ x ω, circC.rel x ω ↔ CFRel bn254 128 g1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) ω)
    -- the curve groups have prime order
    (hord1 : ∀ P : bn254.toAffine.Point, P ≠ 0 → addOrderOf P = r)
    (hord2 : ∀ P : grumpkin.toAffine.Point, P ≠ 0 → addOrderOf P = q)
    (z0 : Fin sN → ZMod r) :
    ∀ (ws : List SW) (zn : Fin sN → ZMod r), Chain StepRel z0 ws zn → ws.length < r →
      ∃ (P : Proof T) (ds : List T.StepData), T.Verify ws.length z0 zn P ∧
        (ws ≠ [] → T.RunOK (fun w => augOutOf grumpkin (circA.decode w)) z0 ws.length zn P ds ∧
          ∃ (D : T.DecOut) (E : T.Extraction), T.DeciderRel ws.length z0 zn D ∧
            T.ExtractionOK (fun w => augOutOf grumpkin (circA.decode w)) ws.length z0 zn D E) := by
  intro ws zn hc hN
  have h2q : (2 : ZMod q) ≠ 0 := by exact_mod_cast natCast_ne_zero (n := q) (by norm_num) (by norm_num [q])
  have h2r : (2 : ZMod r) ≠ 0 := by exact_mod_cast natCast_ne_zero (n := r) (by norm_num) (by norm_num [r])
  exact ivc_complete_of_circuits bn254 grumpkin sponge dS dT rm1 g1 g2 StepRel hp hq hbits T hco hhs
    hch hch2a hch2b hcfx EAc circA hcompA circC hcompC hrelC h2q hord1
    (by norm_num [r]) g1_on h2r hord2 (by norm_num [q]) g2_on (by norm_num [q])
    (by norm_num [r]) (by norm_num [q]) rm1_val (castOK_of_lt hN) z0 ws zn hc le_rfl

end Deployment
end Sonobe
