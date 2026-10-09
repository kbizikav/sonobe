import Sonobe.IVC2.Model

/-!
IVC soundness at the coordinate level (see `Model.lean`): an accepted `n`-step proof forces
`zₙ = Fⁿ(z₀)`.

Assumptions, all explicit hypotheses:
* `AugSound2`  — what a satisfying assignment of the augmented circuit means (to be derived from
  the gadget models); `CFSound2` — same for the CycleFold circuit;
* `HsInj2`     — collision resistance of the state hash (including the public-parameter hash);
* `¬ DLRel`    — binding of the four commitment keys;
* `Fork1'/2'`  — rewinding (forking lemma);
* `CastOK`     — step counts are not multiples of the characteristic.
-/

namespace Sonobe
namespace IVC2

open Nova IVC
open scoped Classical

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] (T : Setup2 F1 G1 F2 G2 S C1)

/-- IVC proof `(W, U, w, u, cf_W, cf_U)`. -/
structure Proof2 where
  W : RunningWitness F1 T.m1 T.nw1
  U : RunningInstance F1 G1 1
  w : IncomingWitness F1 T.nw1
  u : IncomingInstance G1 F1 1
  cfW : RunningWitness F2 T.m2 T.nw2
  cfU : RunningInstance F2 G2 T.l2

/-- What the verifier checks for `n ≥ 1` steps (mod.rs:460-474). -/
def Setup2.Good (n : ℕ) (z0 zn : S) (P : Proof2 T) : Prop :=
  P.u.x = (fun _ => T.hs T.pph (n : F1) z0 zn (T.rawOf P.U) P.cfU) ∧
    T.k1.Running P.U P.W ∧ T.k1.Incoming P.u P.w ∧ T.k2.Running P.cfU P.cfW

def Setup2.AugSound : Prop :=
  ∀ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1), T.k1.Incoming u' w' →
    ∃ (pp i : F1) (z0 zi : S) (U : RawRU F1 C1) (uin : RawIU F1 C1) (π : C1)
      (cfU : RunningInstance F2 G2 T.l2) (cu0 cu1 : IncomingInstance G2 F2 T.l2)
      (cπ0 cπ1 : G2) (cρ0 cρ1 : F2) (pe pw : C1),
      (i = 0 → z0 = zi) ∧ uin.x = (fun _ => T.hs pp i z0 zi U cfU) ∧
      cu0.x = T.cfX (T.ch1n pp U uin π) U.cmE π pe ∧
      cu1.x = T.cfX (T.ch1n pp U uin π) U.cmW uin.cmW pw ∧
      u'.x = (fun _ => T.hs pp (i + 1) z0 (T.step zi)
        (if i = 0 then T.rawOf (dummyRU F1 G1 1)
          else ⟨pe, U.u + T.ch1 pp U uin π, pw, U.x + T.ch1 pp U uin π • uin.x⟩)
        (if i = 0 then dummyRU F2 G2 T.l2
          else foldInstance cρ1 cπ1 (foldInstance cρ0 cπ0 cfU cu0) cu1))

def Setup2.CFSound : Prop :=
  ∀ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 T.l2), T.k2.Incoming cu cw →
    ∀ (n : ℕ) (c0 c1 c2 : C1), n < 2 ^ 128 → cu.x = T.cfX n c0 c1 c2 →
      ∃ P0 P1 P2 : G1, T.coords P0 = c0 ∧ T.coords P1 = c1 ∧ T.coords P2 = c2 ∧
        P2 = P0 + (n : F1) • P1

def Setup2.HsInj : Prop :=
  ∀ pp pp' i i' z0 z0' zi zi' U U' cfU cfU', T.hs pp i z0 zi U cfU = T.hs pp' i' z0' zi' U' cfU' →
    pp = pp' ∧ i = i' ∧ z0 = z0' ∧ zi = zi' ∧ U = U' ∧ cfU = cfU'

def Setup2.Fork1 : Prop :=
  ∀ (ρ : F1) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (W : RunningWitness F1 T.m1 T.nw1), T.k1.Running (foldInstance ρ π U u) W →
    ∃ (ρ₁ ρ₂ ρ₃ : F1) (W₁ W₂ W₃ : RunningWitness F1 T.m1 T.nw1),
      ρ₁ ≠ ρ₂ ∧ ρ₁ ≠ ρ₃ ∧ ρ₂ ≠ ρ₃ ∧ T.k1.Running (foldInstance ρ₁ π U u) W₁ ∧
      T.k1.Running (foldInstance ρ₂ π U u) W₂ ∧ T.k1.Running (foldInstance ρ₃ π U u) W₃

def Setup2.Fork2 : Prop :=
  ∀ (ρ : F2) (U : RunningInstance F2 G2 T.l2) (u : IncomingInstance G2 F2 T.l2) (π : G2)
    (W : RunningWitness F2 T.m2 T.nw2), T.k2.Running (foldInstance ρ π U u) W →
    ∃ (ρ₁ ρ₂ ρ₃ : F2) (W₁ W₂ W₃ : RunningWitness F2 T.m2 T.nw2),
      ρ₁ ≠ ρ₂ ∧ ρ₁ ≠ ρ₃ ∧ ρ₂ ≠ ρ₃ ∧ T.k2.Running (foldInstance ρ₁ π U u) W₁ ∧
      T.k2.Running (foldInstance ρ₂ π U u) W₂ ∧ T.k2.Running (foldInstance ρ₃ π U u) W₃

/-- Step counts up to `N` are non-zero in the field. -/
def CastOK (F1 : Type*) [Field F1] (N : ℕ) : Prop := ∀ n ≤ N, (n : F1) = 0 → n = 0

/-- One backward step of the extraction. -/
theorem sound_step (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK F1 N) (n : ℕ) (hn : n + 1 ≤ N) (z0 zn : S) (P : Proof2 T)
    (hP : T.Good (n + 1) z0 zn P) :
    (n = 0 → zn = T.step z0) ∧
    (n ≠ 0 → ∃ zi P', zn = T.step zi ∧ T.Good n z0 zi P') := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  obtain ⟨pp, i, z0', zi, U, uin, π, cfU, cu0, cu1, cπ0, cπ1, cρ0, cρ1, pe, pw, h0, hux, hx0,
    hx1, hux'⟩ := hA _ _ hu
  have hh := congrFun (hx.symm.trans hux') 0
  obtain ⟨hpp, hi, hz0, hzn, hUeq, hcfeq⟩ := hH _ _ _ _ _ _ _ _ _ _ _ _ hh
  have hi' : i = (n : F1) := by
    push_cast at hi
    exact (add_right_cancel hi).symm
  subst hpp hz0
  refine ⟨fun hn0 => ?_, fun hn0 => ?_⟩
  · subst hn0
    have : i = 0 := by simpa using hi'
    rw [hzn, ← h0 this]
  · have hne : i ≠ 0 := by
      rw [hi']
      intro h
      exact hn0 (hcast n (by omega) h)
    simp only [if_neg hne] at hUeq hcfeq
    -- the secondary side
    rw [hcfeq] at hcf
    obtain ⟨_, _, _, V₁, V₂, V₃, a12, a13, a23, g1, g2, g3⟩ := f2 _ _ _ _ P.cfW hcf
    obtain ⟨X, inc1, hX, hinc1⟩ :=
      fold_sound T.k2 hE2 hW2 (foldInstance cρ0 cπ0 cfU cu0) cu1 cπ1 a12 a13 a23 g1 g2 g3
    obtain ⟨_, _, _, Y₁, Y₂, Y₃, b12, b13, b23, l1, l2, l3⟩ := f2 _ _ _ _ X hX
    obtain ⟨cfW', inc0, hcfW', hinc0⟩ :=
      fold_sound T.k2 hE2 hW2 cfU cu0 cπ0 b12 b13 b23 l1 l2 l3
    -- the CycleFold circuits certify genuine group elements and the fold identities
    obtain ⟨P0, P1, P2, e0, e1, e2, hP2⟩ :=
      hC inc0 cu0 hinc0 _ _ _ _ (T.ch1n_small _ _ _ _) hx0
    obtain ⟨Q0, Q1, Q2, f0, f1', f2', hQ2⟩ :=
      hC inc1 cu1 hinc1 _ _ _ _ (T.ch1n_small _ _ _ _) hx1
    obtain ⟨cmE, ur, cmW, xr⟩ := U
    simp only at e0 f0
    obtain ⟨ucmW, uinx⟩ := uin
    simp only at f1' hux hx0 hx1 hux' hUeq
    set U' : RunningInstance F1 G1 1 := ⟨P0, ur, Q0, xr⟩ with hU'
    set uin' : IncomingInstance G1 F1 1 := ⟨Q1, uinx⟩ with huin'
    have hrawU : T.rawOf U' = ⟨cmE, ur, cmW, xr⟩ := by simp [Setup2.rawOf, hU', e0, f0]
    have hrawI : T.rawOfI uin' = ⟨ucmW, uinx⟩ := by simp [Setup2.rawOfI, huin', f1']
    have hUU : P.U = foldInstance ((T.ch1n T.pph ⟨cmE, ur, cmW, xr⟩ ⟨ucmW, uinx⟩ π : ℕ) : F1) P1 U' uin' := by
      have hc := congrArg RawRU.cmE hUeq
      have hw := congrArg RawRU.cmW hUeq
      have hu := congrArg RawRU.u hUeq
      have hxx := congrArg RawRU.x hUeq
      simp only [Setup2.rawOf, Setup2.ch1] at hc hw hu hxx
      have hP2' : P.U.cmE = P2 := T.coords_inj (hc.trans e2.symm)
      have hQ2' : P.U.cmW = Q2 := T.coords_inj (hw.trans f2'.symm)
      obtain ⟨a, b, c, d, hPU⟩ : ∃ a b c d, P.U = ⟨a, b, c, d⟩ := ⟨_, _, _, _, rfl⟩
      rw [hPU] at hP2' hQ2' hu hxx ⊢
      simp only at hP2' hQ2' hu hxx
      simp only [foldInstance, hU', huin']
      rw [hP2', hQ2', hP2, hQ2, hu, hxx]
    rw [hUU] at hU
    obtain ⟨_, _, _, V₁, V₂, V₃, m12, m13, m23, o1, o2, o3⟩ := f1 _ U' uin' P1 P.W hU
    obtain ⟨Wx, wx, hWx, hwx⟩ := fold_sound T.k1 hE1 hW1 U' uin' P1 m12 m13 m23 o1 o2 o3
    refine ⟨zi, ⟨Wx, U', wx, uin', cfW', cfU⟩, hzn, ?_, hWx, hwx, hcfW'⟩
    show uinx = _
    rw [hux, hi', hrawU]

/-- **IVC soundness (coordinate level)**: an accepted `n+1`-step proof certifies
`z_{n+1} = F^{n+1}(z₀)`. -/
theorem ivc_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel) (f1 : T.Fork1) (f2 : T.Fork2)
    {N : ℕ} (hcast : CastOK F1 N) (z0 : S) :
    ∀ n, n + 1 ≤ N → ∀ (zn : S) (P : Proof2 T), T.Good (n + 1) z0 zn P →
      zn = T.step^[n + 1] z0 := by
  intro n
  induction n with
  | zero =>
    intro hn zn P hP
    simpa using (sound_step T hA hC hH hE1 hW1 hE2 hW2 f1 f2 hcast 0 hn z0 zn P hP).1 rfl
  | succ n ih =>
    intro hn zn P hP
    obtain ⟨zi, P', rfl, hP'⟩ :=
      (sound_step T hA hC hH hE1 hW1 hE2 hW2 f1 f2 hcast (n + 1) hn z0 zn P hP).2 (by omega)
    rw [Function.iterate_succ_apply' T.step (n + 1), ih (by omega) zi P' hP']

end IVC2
end Sonobe
