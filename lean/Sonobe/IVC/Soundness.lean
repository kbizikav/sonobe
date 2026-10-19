import Sonobe.IVC.Model

/-!
IVC soundness at the coordinate level (see `Model.lean`): an accepted `n`-step proof, with the
extraction data of its run, gives witnesses `ws` of the step relation with `Chain R z₀ ws zₙ`.

Assumptions, all explicit hypotheses:
* `AugSound` — what a satisfying assignment of the augmented circuit means, read off its witness
  by a decoder (derived from the gadget models in `Circuit/AugSound.lean`); `CFSound` — same for
  the CycleFold circuit (`Circuit/CFBridge.lean`);
* `RunOK` — about the values of one run, step by step from the last: the hash does not collide on
  the verifier's input and the circuit's (`HashOK`), and every fold the step verified was rewound to
  two more accepting witnesses (`Rewind.Accepts`, the forking lemma) at which binding holds
  (`Rewind.Binds`);
* `CastOK` — step counts are not multiples of the characteristic.

A run that breaks `RunOK` yields a hash collision or, by `PedersenKey.dlRel_of_not_bindsAt`, a
discrete-log relation computed from its values.
-/

namespace Sonobe
namespace IVC

open Nova
open scoped Classical

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- IVC proof `(W, U, w, u, cf_W, cf_U)`. -/
structure Proof where
  W : RunningWitness F1 T.m1 T.nw1
  U : RunningInstance F1 G1 1
  w : IncomingWitness F1 T.nw1
  u : IncomingInstance G1 F1 1
  cfW : RunningWitness F2 T.m2 T.nw2
  cfU : RunningInstance F2 G2 l2

/-- What the verifier checks for `n ≥ 1` steps (mod.rs:460-474). -/
def Setup.Good (n : ℕ) (z0 zn : S) (P : Proof T) : Prop :=
  P.u.x = (fun _ => T.hs T.pph (n : F1) z0 zn (T.rawOf P.U) P.cfU) ∧
    T.k1.Running P.U P.W ∧ T.k1.Incoming P.u P.w ∧ T.k2.Running P.cfU P.cfW

/-! ### The augmented circuit -/

/-- The values of an augmented-circuit assignment that `AugSound` speaks about: the inputs
`(pp, i, z₀, zᵢ, U, u, π, cf_U)`, the next state, the CycleFold instances, proofs and challenges,
and the coordinates `pe`, `pw` of the folded commitments. -/
structure AugOut (F1 F2 G2 S C1 : Type*) (l2 : ℕ) where
  pp : F1
  i : F1
  z0 : S
  zi : S
  nx : S
  U : RawRU F1 C1
  uin : RawIU F1 C1
  π : C1
  cfU : RunningInstance F2 G2 l2
  cu0 : IncomingInstance G2 F2 l2
  cu1 : IncomingInstance G2 F2 l2
  cπ0 : G2
  cπ1 : G2
  cρ0 : F2
  cρ1 : F2
  pe : C1
  pw : C1

/-- The primary challenge of the step. -/
def Setup.chOf (o : AugOut F1 F2 G2 S C1 l2) : F1 := T.ch1 o.pp o.U o.uin o.π

/-- The primary running instance hashed into the output: the fold, or the dummy in the base
case. -/
noncomputable def Setup.outU (o : AugOut F1 F2 G2 S C1 l2) : RawRU F1 C1 :=
  if o.i = 0 then T.rawOf (dummyRU F1 G1 1)
  else ⟨o.pe, o.U.u + T.chOf o, o.pw, o.U.x + T.chOf o • o.uin.x⟩

/-- The secondary running instance after the first CycleFold fold. -/
def AugOut.cfMid (o : AugOut F1 F2 G2 S C1 l2) : RunningInstance F2 G2 l2 :=
  foldInstance o.cρ0 o.cπ0 o.cfU o.cu0

/-- The secondary running instance hashed into the output. -/
noncomputable def AugOut.outCf (o : AugOut F1 F2 G2 S C1 l2) : RunningInstance F2 G2 l2 :=
  if o.i = 0 then dummyRU F2 G2 l2 else foldInstance o.cρ1 o.cπ1 o.cfMid o.cu1

/-- What the augmented circuit enforces between its decoded values `o` and its public output
`ux`, for the step relation `R`. -/
def Setup.AugFacts {SW : Type*} (R : S → SW → S → Prop) (o : AugOut F1 F2 G2 S C1 l2)
    (ux : Fin 1 → F1) : Prop :=
  (o.i = 0 → o.z0 = o.zi) ∧ (∃ sw, R o.zi sw o.nx) ∧
    o.uin.x = (fun _ => T.hs o.pp o.i o.z0 o.zi o.U o.cfU) ∧
    o.cu0.x = T.cfX (T.ch1n o.pp o.U o.uin o.π) o.U.cmE o.π o.pe ∧
    o.cu1.x = T.cfX (T.ch1n o.pp o.U o.uin o.π) o.U.cmW o.uin.cmW o.pw ∧
    ux = (fun _ => T.hs o.pp (o.i + 1) o.z0 o.nx (T.outU o) o.outCf)

/-- The augmented circuit is sound: the values `dec` reads off any satisfying witness meet
`AugFacts`. -/
def Setup.AugSound {SW : Type*} (R : S → SW → S → Prop)
    (dec : (Fin T.nw1 → F1) → AugOut F1 F2 G2 S C1 l2) : Prop :=
  ∀ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1), T.k1.Incoming u' w' →
    T.AugFacts R (dec w'.w) u'.x

def Setup.CFSound : Prop :=
  ∀ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 l2), T.k2.Incoming cu cw →
    ∀ (n : ℕ) (c0 c1 c2 : C1), n < 2 ^ 128 → cu.x = T.cfX n c0 c1 c2 →
      ∃ P0 P1 P2 : G1, T.coords P0 = c0 ∧ T.coords P1 = c1 ∧ T.coords P2 = c2 ∧
        P2 = P0 + (n : F1) • P1

/-! ### Per-run hypotheses -/

/-- The state hash does not collide on these two inputs. -/
def Setup.HsAt (pp i : F1) (z0 zi : S) (U : RawRU F1 C1) (cfU : RunningInstance F2 G2 l2)
    (pp' i' : F1) (z0' zi' : S) (U' : RawRU F1 C1) (cfU' : RunningInstance F2 G2 l2) : Prop :=
  T.hs pp i z0 zi U cfU = T.hs pp' i' z0' zi' U' cfU' →
    pp = pp' ∧ i = i' ∧ z0 = z0' ∧ zi = zi' ∧ U = U' ∧ cfU = cfU'

/-- The rewindings of one step's three folds: the primary fold and the two CycleFold folds its
augmented circuit verified. -/
structure Setup.StepData where
  r1 : Rewind F1 T.m1 T.nw1
  r2a : Rewind F2 T.m2 T.nw2
  r2b : Rewind F2 T.m2 T.nw2

variable (dec : (Fin T.nw1 → F1) → AugOut F1 F2 G2 S C1 l2)

/-- The primary running instance the step folded, as points. -/
noncomputable def Setup.inU (o : AugOut F1 F2 G2 S C1 l2) : RunningInstance F1 G1 1 :=
  ⟨T.pt o.U.cmE, o.U.u, T.pt o.U.cmW, o.U.x⟩

/-- The primary incoming instance the step folded, as points. -/
noncomputable def Setup.inu (o : AugOut F1 F2 G2 S C1 l2) : IncomingInstance G1 F1 1 :=
  ⟨T.pt o.uin.cmW, o.uin.x⟩

/-- The extracted witness of `cf_mid` and of `cf_u₁` (second CycleFold fold). -/
def Setup.ext2b (P : Proof T) (d : T.StepData) :
    RunningWitness F2 T.m2 T.nw2 × IncomingWitness F2 T.nw2 :=
  d.r2b.extract (dec P.w.w).cρ1 P.cfW

/-- **One backward step**: the proof of the previous step, extracted from `P` and the rewindings
of the step's folds. -/
noncomputable def Setup.back (P : Proof T) (d : T.StepData) : Proof T :=
  ⟨(d.r1.extract (T.chOf (dec P.w.w)) P.W).1, T.inU (dec P.w.w),
    (d.r1.extract (T.chOf (dec P.w.w)) P.W).2, T.inu (dec P.w.w),
    (d.r2a.extract (dec P.w.w).cρ0 (T.ext2b dec P d).1).1, (dec P.w.w).cfU⟩

/-- The rewindings of a step's folds are accepting and break no binding. -/
def Setup.ForkOK (P : Proof T) (d : T.StepData) : Prop :=
  d.r2b.Accepts T.k2 (dec P.w.w).cfMid (dec P.w.w).cu1 (dec P.w.w).cπ1 (dec P.w.w).cρ1 ∧
    d.r2b.Binds T.k2 (dec P.w.w).cρ1 P.cfW ∧
    d.r2a.Accepts T.k2 (dec P.w.w).cfU (dec P.w.w).cu0 (dec P.w.w).cπ0 (dec P.w.w).cρ0 ∧
    d.r2a.Binds T.k2 (dec P.w.w).cρ0 (T.ext2b dec P d).1 ∧
    d.r1.Accepts T.k1 (T.inU (dec P.w.w)) (T.inu (dec P.w.w)) (T.pt (dec P.w.w).π)
      (T.chOf (dec P.w.w)) ∧
    d.r1.Binds T.k1 (T.chOf (dec P.w.w)) P.W

/-- The step's hash does not collide on the verifier's input and the circuit's. -/
def Setup.HashOK (n : ℕ) (z0 zn : S) (P : Proof T) : Prop :=
  T.HsAt T.pph (n : F1) z0 zn (T.rawOf P.U) P.cfU (dec P.w.w).pp ((dec P.w.w).i + 1)
    (dec P.w.w).z0 (dec P.w.w).nx (T.outU (dec P.w.w)) (dec P.w.w).outCf

/-- **The run's hypotheses.** The extraction data `ds` (one entry per step but the first, from the
last back) fits the run back from `P`, a proof of `(n, z₀, zₙ)`: at every step the hash does not
collide (`HashOK`), and the rewindings of its folds are accepting and break no binding
(`ForkOK`). The first step's folds are of dummies, so it needs no rewinding. -/
def Setup.RunOK (z0 : S) : ℕ → S → Proof T → List T.StepData → Prop
  | 1, zn, P, [] => T.HashOK dec 1 z0 zn P
  | n + 2, zn, P, d :: ds => T.HashOK dec (n + 2) z0 zn P ∧ T.ForkOK dec P d ∧
      Setup.RunOK z0 (n + 1) (dec P.w.w).zi (T.back dec P d) ds
  | _, _, _, _ => False

/-- Step counts up to `N` are non-zero in the field. -/
def CastOK (F1 : Type*) [Field F1] (N : ℕ) : Prop := ∀ n ≤ N, (n : F1) = 0 → n = 0

/-! ### Soundness -/

variable {SW : Type*} {R : S → SW → S → Prop}

/-- One backward step of the extraction. -/
theorem sound_step (hA : T.AugSound R dec) (hC : T.CFSound) {N : ℕ} (hcast : CastOK F1 N) (n : ℕ)
    (hn : n + 1 ≤ N) (z0 zn : S) (P : Proof T) (hP : T.Good (n + 1) z0 zn P)
    (hH : T.HashOK dec (n + 1) z0 zn P) :
    (∃ sw, R (dec P.w.w).zi sw zn) ∧ (n = 0 → (dec P.w.w).zi = z0) ∧
      (n ≠ 0 → ∀ d, T.ForkOK dec P d → T.Good n z0 (dec P.w.w).zi (T.back dec P d)) := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  set o := dec P.w.w with ho
  obtain ⟨h0, ⟨sw, hR⟩, hux, hx0, hx1, hux'⟩ := hA _ _ hu
  rw [← ho] at h0 hR hux hx0 hx1 hux'
  have hh := congrFun (hx.symm.trans hux') 0
  obtain ⟨hpp, hi, hz0, hzn, hUeq, hcfeq⟩ := hH hh
  rw [← ho] at hpp hi hz0 hzn hUeq hcfeq
  have hi' : o.i = (n : F1) := by
    push_cast at hi
    exact (add_right_cancel hi).symm
  rw [← hzn] at hR
  refine ⟨⟨sw, hR⟩, fun hn0 => ?_, fun hn0 d hd => ?_⟩
  · subst hn0
    have : o.i = 0 := by simpa using hi'
    rw [hz0, h0 this]
  have hne : o.i ≠ 0 := by
    rw [hi']
    intro h
    exact hn0 (hcast n (by omega) h)
  obtain ⟨ha2b, hb2b, ha2a, hb2a, ha1, hb1⟩ := hd
  rw [← ho] at ha2b hb2b ha2a hb2a ha1 hb1
  -- the secondary side
  simp only [AugOut.outCf, if_neg hne] at hcfeq
  rw [hcfeq] at hcf
  obtain ⟨hX, hinc1⟩ := Rewind.sound T.k2 hcf ha2b hb2b
  have hX' : T.k2.Running (foldInstance o.cρ0 o.cπ0 o.cfU o.cu0) (T.ext2b dec P d).1 := hX
  obtain ⟨hcfW', hinc0⟩ := Rewind.sound T.k2 hX' ha2a hb2a
  -- the CycleFold circuits certify genuine group elements and the fold identities
  obtain ⟨P0, P1, P2, e0, e1, e2, hP2⟩ := hC _ _ hinc0 _ _ _ _ (T.ch1n_small _ _ _ _) hx0
  obtain ⟨Q0, Q1, Q2, f0, f1, f2, hQ2⟩ := hC _ _ hinc1 _ _ _ _ (T.ch1n_small _ _ _ _) hx1
  have pE : T.pt o.U.cmE = P0 := by rw [← e0, T.pt_coords]
  have pπ : T.pt o.π = P1 := by rw [← e1, T.pt_coords]
  have pW : T.pt o.U.cmW = Q0 := by rw [← f0, T.pt_coords]
  have pu : T.pt o.uin.cmW = Q1 := by rw [← f1, T.pt_coords]
  have hrawU : T.rawOf (T.inU o) = o.U := by
    simp only [Setup.rawOf, Setup.inU, pE, pW, e0, f0]
  have hUU : P.U = foldInstance (T.chOf o) (T.pt o.π) (T.inU o) (T.inu o) := by
    simp only [Setup.outU, if_neg hne] at hUeq
    have hc := congrArg RawRU.cmE hUeq
    have hw := congrArg RawRU.cmW hUeq
    have hu' := congrArg RawRU.u hUeq
    have hxx := congrArg RawRU.x hUeq
    simp only [Setup.rawOf] at hc hw hu' hxx
    have hP2' : P.U.cmE = P2 := T.coords_inj (hc.trans e2.symm)
    have hQ2' : P.U.cmW = Q2 := T.coords_inj (hw.trans f2.symm)
    obtain ⟨a, b, c, x, hPU⟩ : ∃ a b c x, P.U = ⟨a, b, c, x⟩ := ⟨_, _, _, _, rfl⟩
    rw [hPU] at hP2' hQ2' hu' hxx ⊢
    simp only at hP2' hQ2' hu' hxx
    simp only [foldInstance, Setup.inU, Setup.inu, Setup.chOf, Setup.ch1, pE, pπ, pW, pu]
    rw [hP2', hQ2', hP2, hQ2, hu', hxx]
    rfl
  rw [hUU] at hU
  obtain ⟨hWx, hwx⟩ := Rewind.sound T.k1 hU ha1 hb1
  refine ⟨?_, hWx, hwx, hcfW'⟩
  show (T.inu o).x = fun _ => T.hs T.pph (n : F1) z0 o.zi (T.rawOf (T.inU o)) o.cfU
  simp only [Setup.inu]
  rw [hux, hrawU, ← hpp, ← hz0, hi']

/-- **IVC soundness (coordinate level)**: an accepted `n+1`-step proof whose run meets `RunOK`
gives `n + 1` witnesses of the step relation chaining `z₀` to `z_{n+1}`. -/
theorem ivc_sound (hA : T.AugSound R dec) (hC : T.CFSound) {N : ℕ} (hcast : CastOK F1 N)
    (z0 : S) :
    ∀ n, n + 1 ≤ N → ∀ (zn : S) (P : Proof T) (ds : List T.StepData), T.Good (n + 1) z0 zn P →
      T.RunOK dec z0 (n + 1) zn P ds → ∃ ws : List SW, ws.length = n + 1 ∧ Chain R z0 ws zn := by
  intro n
  induction n with
  | zero =>
    intro hn zn P ds hP hrun
    cases ds with
    | nil =>
      obtain ⟨⟨sw, hR⟩, h0, -⟩ := sound_step T dec hA hC hcast 0 hn z0 zn P hP hrun
      rw [h0 rfl] at hR
      exact ⟨[sw], rfl, Chain.cons hR (Chain.nil _)⟩
    | cons d ds => exact absurd hrun (by simp [Setup.RunOK])
  | succ n ih =>
    intro hn zn P ds hP hrun
    cases ds with
    | nil => exact absurd hrun (by simp [Setup.RunOK])
    | cons d ds =>
      obtain ⟨hH, hF, hrun'⟩ := hrun
      obtain ⟨⟨sw, hR⟩, -, hback⟩ := sound_step T dec hA hC hcast (n + 1) hn z0 zn P hP hH
      obtain ⟨ws, hlen, hc⟩ := ih (by omega) _ _ ds (hback (by omega) d hF) hrun'
      exact ⟨ws ++ [sw], by simp [hlen], hc.snoc hR⟩

end IVC
end Sonobe
