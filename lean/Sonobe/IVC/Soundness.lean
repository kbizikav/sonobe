import Sonobe.IVC.Completeness
import Sonobe.Nova.Soundness

/-!
IVC soundness (algebraic part): an accepted proof of `n` steps forces `zₙ = Fⁿ(z₀)`.

Explicit assumptions (everything the cryptographic model has to supply):
* `AugSound` / `CFSound`: what a satisfying assignment of the augmented / CycleFold circuit means
  (to be discharged by the constraint-level development of the gadgets);
* `HsInj`: collision resistance of the state hash on its (injectively encoded) inputs;
* `¬ DLRel` for the four commitment keys (binding);
* `Fork1`/`Fork2`: rewinding — an accepting fold can be re-run on three distinct challenges
  (the forking lemma, not proved here).
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] (T : Setup F1 G1 F2 G2 S)

/-- CycleFold circuit soundness: its public inputs encode a correct `P₂ = P₀ + ρ P₁`. -/
def Setup.CFSound : Prop :=
  ∀ (cw : IncomingWitness F2 T.nw2) (cu : IncomingInstance G2 F2 T.l2), T.k2.Incoming cu cw →
    ∀ (ρ : F1) (P0 P1 P2 : G1), cu.x = T.cfX ρ P0 P1 P2 → P2 = P0 + ρ • P1

/-- Augmented circuit soundness (circuits.rs:93-195): a satisfying assignment exposes the data of
one step. The new commitments `pe, pw` of `UU` are *free* witnesses of the circuit; they are tied
to the fold only through the CycleFold public inputs `cu0.x`, `cu1.x`. -/
def Setup.AugSound : Prop :=
  ∀ (w' : IncomingWitness F1 T.nw1) (u' : IncomingInstance G1 F1 1), T.k1.Incoming u' w' →
    ∃ (i : ℕ) (z0 zi : S) (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
      (cfU : RunningInstance F2 G2 T.l2) (cu0 cu1 : IncomingInstance G2 F2 T.l2) (cπ0 cπ1 : G2)
      (pe pw : G1),
      (i = 0 → z0 = zi) ∧ u.x = (fun _ => T.hs i z0 zi U cfU) ∧
      cu0.x = T.cfX (T.ch1 U u π) U.cmE π pe ∧ cu1.x = T.cfX (T.ch1 U u π) U.cmW u.cmW pw ∧
      u'.x = (fun _ => T.hs (i + 1) z0 (T.step zi)
        (if i = 0 then dummyRU F1 G1 1 else
          ⟨pe, U.u + T.ch1 U u π, pw, U.x + T.ch1 U u π • u.x⟩)
        (if i = 0 then dummyRU F2 G2 T.l2 else T.fold2 (T.fold2 cfU cu0 cπ0) cu1 cπ1))

def Setup.HsInj : Prop :=
  ∀ i i' z0 z0' zi zi' U U' cfU cfU', T.hs i z0 zi U cfU = T.hs i' z0' zi' U' cfU' →
    i = i' ∧ z0 = z0' ∧ zi = zi' ∧ U = U' ∧ cfU = cfU'

def Setup.Fork1 : Prop :=
  ∀ (U : RunningInstance F1 G1 1) (u : IncomingInstance G1 F1 1) (π : G1)
    (W : RunningWitness F1 T.m1 T.nw1), T.k1.Running (T.fold1 U u π) W →
    ∃ (ρ₁ ρ₂ ρ₃ : F1) (W₁ W₂ W₃ : RunningWitness F1 T.m1 T.nw1),
      ρ₁ ≠ ρ₂ ∧ ρ₁ ≠ ρ₃ ∧ ρ₂ ≠ ρ₃ ∧ T.k1.Running (foldInstance ρ₁ π U u) W₁ ∧
      T.k1.Running (foldInstance ρ₂ π U u) W₂ ∧ T.k1.Running (foldInstance ρ₃ π U u) W₃

def Setup.Fork2 : Prop :=
  ∀ (U : RunningInstance F2 G2 T.l2) (u : IncomingInstance G2 F2 T.l2) (π : G2)
    (W : RunningWitness F2 T.m2 T.nw2), T.k2.Running (T.fold2 U u π) W →
    ∃ (ρ₁ ρ₂ ρ₃ : F2) (W₁ W₂ W₃ : RunningWitness F2 T.m2 T.nw2),
      ρ₁ ≠ ρ₂ ∧ ρ₁ ≠ ρ₃ ∧ ρ₂ ≠ ρ₃ ∧ T.k2.Running (foldInstance ρ₁ π U u) W₁ ∧
      T.k2.Running (foldInstance ρ₂ π U u) W₂ ∧ T.k2.Running (foldInstance ρ₃ π U u) W₃

/-- One backward step: an accepting `Good (n+1)` proof exposes the previous step's data;
if `n ≠ 0` the previous `(U, u, cf_U)` are again satisfiable, so the induction can continue. -/
theorem sound_step (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel)
    (f1 : T.Fork1) (f2 : T.Fork2) (n : ℕ) (z0 zn : S) (P : Proof T)
    (hP : T.Good (n + 1) z0 zn P) :
    (n = 0 → zn = T.step z0) ∧
    (n ≠ 0 → ∃ zi P', zn = T.step zi ∧ T.Good n z0 zi P') := by
  obtain ⟨hx, hU, hu, hcf⟩ := hP
  obtain ⟨i, z0', zi, U, u, π, cfU, cu0, cu1, cπ0, cπ1, pe, pw, h0, hux, hx0, hx1, hux'⟩ :=
    hA _ _ hu
  have hh := congrFun (hx.symm.trans hux') 0
  obtain ⟨hi, hz0, hzn, hUeq, hcfeq⟩ := hH _ _ _ _ _ _ _ _ _ _ hh
  have hin : i = n := by omega
  subst hin hz0 hzn
  refine ⟨fun hi0 => by rw [h0 hi0], fun hn => ?_⟩
  simp only [if_neg hn] at hUeq hcfeq
  -- extract the CycleFold side
  rw [hcfeq] at hcf
  obtain ⟨_, _, _, W₁, W₂, W₃, h12, h13, h23, g1, g2, g3⟩ :=
    f2 _ cu1 cπ1 P.cfW hcf
  obtain ⟨X, inc1, hX, hinc1⟩ :=
    fold_sound T.k2 hE2 hW2 (T.fold2 cfU cu0 cπ0) cu1 cπ1 h12 h13 h23 g1 g2 g3
  obtain ⟨_, _, _, V₁, V₂, V₃, k12, k13, k23, l1, l2, l3⟩ := f2 _ cu0 cπ0 X hX
  obtain ⟨cfW', inc0, hcfW', hinc0⟩ :=
    fold_sound T.k2 hE2 hW2 cfU cu0 cπ0 k12 k13 k23 l1 l2 l3
  -- the commitments of `UU` are the genuine fold
  have hpe := hC inc0 cu0 hinc0 _ _ _ _ hx0
  have hpw := hC inc1 cu1 hinc1 _ _ _ _ hx1
  have hUU : P.U = T.fold1 U u π := by
    rw [hUeq, hpe, hpw]; rfl
  rw [hUU] at hU
  -- extract the primary side
  obtain ⟨_, _, _, V₁, V₂, V₃, m12, m13, m23, o1, o2, o3⟩ := f1 U u π P.W hU
  obtain ⟨Wx, wx, hWx, hwx⟩ := fold_sound T.k1 hE1 hW1 U u π m12 m13 m23 o1 o2 o3
  exact ⟨zi, ⟨Wx, U, wx, u, cfW', cfU⟩, rfl, hux, hWx, hwx, hcfW'⟩

/-- **IVC soundness**: an accepted `n+1`-step proof certifies `z_{n+1} = F^{n+1}(z₀)`. -/
theorem ivc_sound (hA : T.AugSound) (hC : T.CFSound) (hH : T.HsInj)
    (hE1 : ¬ T.k1.ckE.DLRel) (hW1 : ¬ T.k1.ckW.DLRel)
    (hE2 : ¬ T.k2.ckE.DLRel) (hW2 : ¬ T.k2.ckW.DLRel)
    (f1 : T.Fork1) (f2 : T.Fork2) (z0 : S) :
    ∀ n (zn : S) (P : Proof T), T.Good (n + 1) z0 zn P → zn = T.step^[n + 1] z0 := by
  intro n
  induction n with
  | zero =>
    intro zn P hP
    simpa using (sound_step T hA hC hH hE1 hW1 hE2 hW2 f1 f2 0 z0 zn P hP).1 rfl
  | succ n ih =>
    intro zn P hP
    obtain ⟨zi, P', rfl, hP'⟩ :=
      (sound_step T hA hC hH hE1 hW1 hE2 hW2 f1 f2 (n + 1) z0 zn P hP).2 (by omega)
    rw [Function.iterate_succ_apply' T.step (n + 1), ih zi P' hP']

end IVC
end Sonobe
