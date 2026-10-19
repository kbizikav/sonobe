import Sonobe.IVC.Soundness

/-!
IVC completeness at the coordinate level: an honest prover, running the folding schemes and the
(specified) circuits, always produces a proof the verifier accepts (mod.rs:310-421 against
mod.rs:431-477).

The circuits are kept behind `AugComplete` and `CFComplete`, the completeness counterparts of
`AugSound` and `CFSound`.
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- First secondary fold of a step (verifier side): the challenge is derived from the transcript,
which contains the primary data. -/
def Setup.cfFold1 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 : IncomingInstance G2 F2 l2) (cπ0 : G2) :
    RunningInstance F2 G2 l2 :=
  foldInstance ((T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : F2) cπ0
    cfU cu0

/-- Second secondary fold of a step. -/
def Setup.cfFold2 (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (cfU : RunningInstance F2 G2 l2) (cu0 : IncomingInstance G2 F2 l2) (cπ0 : G2)
    (cu1 : IncomingInstance G2 F2 l2) (cπ1 : G2) : RunningInstance F2 G2 l2 :=
  foldInstance ((T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 : ℕ) : F2)
    cπ1 (T.cfFold1 U u π cfU cu0 cπ0) cu1

/-- Public output of the augmented circuit (circuits.rs:187-194): `H(pp, i+1, z₀, z_{i+1}, UU, cf_UU)`
with the dummies selected in the base case. -/
def Setup.augOut (i : ℕ) (z0 nx : S) (U : RunningInstance F1 G1 1)
    (u : IncomingInstance G1 F1 1) (π : G1) (cfU : RunningInstance F2 G2 l2)
    (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2) : F1 :=
  T.hs T.pph ((i + 1 : ℕ) : F1) z0 nx
    (if i = 0 then T.rawOf (dummyRU F1 G1 1) else T.rawOf (T.fold1 U u π))
    (if i = 0 then dummyRU F2 G2 l2 else T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1)

/-- Circuit completeness: for a step `R zᵢ w z_{i+1}` and the honest CycleFold inputs, the augmented
circuit has a satisfying assignment, whose public input is `augOut`. -/
def Setup.AugComplete {SW : Type*} (R : S → SW → S → Prop) : Prop :=
  ∀ (i : ℕ) (z0 zi nx : S) (sw : SW) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1)
    (π : G1) (cfU : RunningInstance F2 G2 l2) (cu0 cu1 : IncomingInstance G2 F2 l2) (cπ0 cπ1 : G2),
    R zi sw nx → (((i : ℕ) : F1) = 0 → i = 0) → (i = 0 → z0 = zi) →
    u.x = (fun _ => T.hs T.pph (i : F1) z0 zi (T.rawOf U) cfU) →
    cu0.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmE)
      (T.coords π) (T.coords (T.fold1 U u π).cmE) →
    cu1.x = T.cfX (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords π)) (T.coords U.cmW)
      (T.coords u.cmW) (T.coords (T.fold1 U u π).cmW) →
    ∃ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1),
      T.k1.Incoming u' w' ∧ u'.x = fun _ => T.augOut i z0 nx U u π cfU cu0 cu1 cπ0 cπ1

/-- CycleFold circuit completeness: `P₂ = P₀ + ρ P₁` is satisfiable with public input `cfX`. -/
def Setup.CFComplete : Prop :=
  ∀ (n : ℕ) (P0 P1 P2 : G1), n < 2 ^ 128 → P2 = P0 + (n : F1) • P1 →
    ∃ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 l2),
      T.k2.Incoming cu cw ∧ cu.x = T.cfX n (T.coords P0) (T.coords P1) (T.coords P2)

/-- `IVCVerifier::verify` (mod.rs:431), after the shape checks. -/
def Setup.Verify (i : ℕ) (z0 zi : S) (P : Proof T) : Prop :=
  if i = 0 then z0 = zi else T.Good i z0 zi P

variable {SW : Type*} {R : S → SW → S → Prop}

/-- Base case `i = 0` (mod.rs:358 skipped; the circuit runs on dummies). -/
theorem prove_base (hA : T.AugComplete R) (hC : T.CFComplete) {z0 z1 : S} {sw : SW}
    (hR : R z0 sw z1) : ∃ P : Proof T, T.Good 1 z0 z1 P := by
  set U := dummyRU F1 G1 1
  set cfU := dummyRU F2 G2 l2
  set u : IncomingInstance G1 F1 1 :=
    ⟨0, fun _ => T.hs T.pph (((0 : ℕ)) : F1) z0 z0 (T.rawOf U) cfU⟩ with hu
  obtain ⟨cw0, cu0, -, hx0⟩ := hC (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords 0)) U.cmE 0
    (T.fold1 U u 0).cmE (T.ch1n_small _ _ _ _) rfl
  obtain ⟨cw1, cu1, -, hx1⟩ := hC (T.ch1n T.pph (T.rawOf U) (T.rawOfI u) (T.coords 0)) U.cmW
    u.cmW (T.fold1 U u 0).cmW (T.ch1n_small _ _ _ _) rfl
  obtain ⟨w', u', hu', hxu'⟩ :=
    hA 0 z0 z0 z1 sw U u 0 cfU cu0 cu1 0 0 hR (fun _ => rfl) (fun _ => rfl) rfl hx0 hx1
  refine ⟨⟨dummyRW F1 T.m1 T.nw1, U, w', u', dummyRW F2 T.m2 T.nw2, cfU⟩, ?_, running_dummy _,
    hu', running_dummy _⟩
  simp [hxu', Setup.augOut]
  rfl

/-- One honest prover step from a satisfying `(U, W, u, w, cf_U, cf_W)` (`n ≥ 1`). -/
theorem prove_succ (hA : T.AugComplete R) (hC : T.CFComplete) (n : ℕ) (hnc : ((n : ℕ) : F1) ≠ 0)
    (z0 zn : S) {zn' : S} {sw : SW} (hR : R zn sw zn')
    (P : Proof T) (hP : T.Good n z0 zn P) :
    ∃ P' : Proof T, T.Good (n + 1) z0 zn' P' := by
  have hn : n ≠ 0 := fun h => hnc (by rw [h]; simp)
  obtain ⟨hxu, hU, hu, hcf⟩ := hP
  set U := P.U; set W := P.W; set u := P.u; set w := P.w; set cfU := P.cfU; set cfW := P.cfW
  -- primary fold
  set π := T.k1.ckE.commit (crossTerm T.k1 U W u w) 0 with hπ
  set ρ := T.ch1 T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) with hρ
  have hUU := fold_complete T.k1 hU hu ρ 0
  -- the two CycleFold circuits
  obtain ⟨cw0, cu0, hcu0, hx0⟩ := hC _ U.cmE π (T.fold1 U u π).cmE (T.ch1n_small _ _ _ _) rfl
  obtain ⟨cw1, cu1, hcu1, hx1⟩ := hC _ U.cmW u.cmW (T.fold1 U u π).cmW (T.ch1n_small _ _ _ _) rfl
  set cπ0 := T.k2.ckE.commit (crossTerm T.k2 cfU cfW cu0 cw0) 0 with hcπ0
  set ρ0 : F2 := ((T.ch2an T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 : ℕ) : F2)
    with hρ0
  have hf0 := fold_complete T.k2 hcf hcu0 ρ0 0
  set cfU1 := T.cfFold1 U u π cfU cu0 cπ0 with hcfU1
  set cfW1 := foldWitness ρ0 0 (crossTerm T.k2 cfU cfW cu0 cw0) cfW cw0
  set cπ1 := T.k2.ckE.commit (crossTerm T.k2 cfU1 cfW1 cu1 cw1) 0
  set ρ1 : F2 := ((T.ch2bn T.pph (T.rawOf U) (T.rawOfI u) (T.coords π) cfU cu0 cπ0 cu1 cπ1 : ℕ) : F2)
    with hρ1
  have hf1 := fold_complete T.k2 hf0 hcu1 ρ1 0
  obtain ⟨w', u', hu', hxu'⟩ := hA n z0 zn zn' sw U u π cfU cu0 cu1 cπ0 cπ1 hR
    (fun h => absurd h hnc) (fun h => absurd h hn) hxu hx0 hx1
  refine ⟨⟨_, T.fold1 U u π, w', u', _, T.cfFold2 U u π cfU cu0 cπ0 cu1 cπ1⟩, ?_, hUU, hu', hf1⟩
  simp [hn, hxu', Setup.augOut]

/-- **IVC completeness**: for every chain of `n ≤ N` steps (step counts that are non-zero in the
field) there is an accepting proof of `(n, z₀, zₙ)`. -/
theorem ivc_complete (hA : T.AugComplete R) (hC : T.CFComplete) {N : ℕ} (hcast : CastOK F1 N)
    (z0 : S) : ∀ (ws : List SW) (zn : S), Chain R z0 ws zn → ws.length ≤ N →
      ∃ P : Proof T, T.Verify ws.length z0 zn P := by
  have good : ∀ (ws : List SW) (zn : S), Chain R z0 ws zn → ws ≠ [] → ws.length ≤ N →
      ∃ P : Proof T, T.Good ws.length z0 zn P := by
    intro ws
    induction ws using List.reverseRecOn with
    | nil => intro _ _ h; exact absurd rfl h
    | append_singleton ws sw ih =>
      intro zn hc _ hN
      obtain ⟨zm, hcm, hR⟩ := Chain.of_snoc hc
      by_cases hne : ws = []
      · subst hne
        cases hcm
        exact prove_base T hA hC hR
      · obtain ⟨P, hP⟩ := ih zm hcm hne (by simp at hN; omega)
        have hl : ws.length ≠ 0 := by simpa using hne
        simpa using prove_succ T hA hC ws.length
          (fun h => hl (hcast _ (by simp at hN; omega) h)) z0 zm hR P hP
  intro ws zn hc hN
  by_cases hne : ws = []
  · subst hne
    cases hc
    exact ⟨⟨dummyRW F1 T.m1 T.nw1, dummyRU F1 G1 1, ⟨0, 0⟩, ⟨0, fun _ => 0⟩, dummyRW F2 T.m2 T.nw2,
      dummyRU F2 G2 l2⟩, by simp [Setup.Verify]⟩
  · obtain ⟨P, hP⟩ := good ws zn hc hne hN
    exact ⟨P, by simpa [Setup.Verify, List.length_eq_zero_iff, hne] using hP⟩

end IVC
end Sonobe
