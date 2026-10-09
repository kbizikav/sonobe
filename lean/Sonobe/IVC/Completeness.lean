import Sonobe.IVC.Model

/-!
IVC completeness: an honest prover, running the folding schemes and the (specified) circuits, always
produces a proof the verifier accepts (mod.rs:310-421 against mod.rs:431-477).
-/

namespace Sonobe
namespace IVC

open Nova

variable {F1 G1 F2 G2 S : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] (T : Setup F1 G1 F2 G2 S)

/-- Facts the verifier checks for `n ≥ 1` steps. -/
def Setup.Good (n : ℕ) (z0 zn : S) (P : Proof T) : Prop :=
  P.u.x = (fun _ => T.hs n z0 zn P.U P.cfU) ∧ T.k1.Running P.U P.W ∧
    T.k1.Incoming P.u P.w ∧ T.k2.Running P.cfU P.cfW

/-- Base case `i = 0` (mod.rs:358 skipped; the circuit runs on dummies). -/
theorem prove_base (hA : T.AugComplete) (hC : T.CFComplete) (z0 : S) :
    ∃ P : Proof T, T.Good 1 z0 (T.step z0) P := by
  set U := dummyRU F1 G1 1
  set u : IncomingInstance G1 F1 1 := ⟨0, fun _ => 0⟩
  set cfU := dummyRU F2 G2 T.l2
  obtain ⟨cw0, cu0, -, hx0⟩ := hC (T.ch1 U u 0) U.cmE 0 (T.fold1 U u 0).cmE rfl
  obtain ⟨cw1, cu1, -, hx1⟩ := hC (T.ch1 U u 0) U.cmW u.cmW (T.fold1 U u 0).cmW rfl
  obtain ⟨w', u', hu', hxu'⟩ := hA 0 z0 z0 U u 0 cfU cu0 cu1 0 0 (fun _ => rfl) hx0 hx1
  refine ⟨⟨dummyRW F1 T.m1 T.nw1, U, w', u', dummyRW F2 T.m2 T.nw2, cfU⟩, ?_, running_dummy _,
    hu', running_dummy _⟩
  simp [hxu', Setup.augOut]
  rfl

/-- One honest prover step from a satisfying `(U, W, u, w, cf_U, cf_W)` (`n ≥ 1`). -/
theorem prove_succ (hA : T.AugComplete) (hC : T.CFComplete) (n : ℕ) (hn : n ≠ 0) (z0 zn : S)
    (P : Proof T) (hP : T.Good n z0 zn P) : ∃ P' : Proof T, T.Good (n + 1) z0 (T.step zn) P' := by
  obtain ⟨-, hU, hu, hcf⟩ := hP
  set U := P.U; set W := P.W; set u := P.u; set w := P.w; set cfU := P.cfU; set cfW := P.cfW
  -- primary fold
  set π := T.k1.ckE.commit (crossTerm T.k1 U W u w) 0 with hπ
  set ρ := T.ch1 U u π with hρ
  have hUU := fold_complete T.k1 hU hu ρ 0
  -- the two CycleFold circuits
  obtain ⟨cw0, cu0, hcu0, hx0⟩ := hC ρ U.cmE π (T.fold1 U u π).cmE rfl
  obtain ⟨cw1, cu1, hcu1, hx1⟩ := hC ρ U.cmW u.cmW (T.fold1 U u π).cmW rfl
  set cπ0 := T.k2.ckE.commit (crossTerm T.k2 cfU cfW cu0 cw0) 0
  have hf0 := fold_complete T.k2 hcf hcu0 (T.ch2 cfU cu0 cπ0) 0
  set cfU1 := T.fold2 cfU cu0 cπ0
  set cfW1 := foldWitness (T.ch2 cfU cu0 cπ0) 0 (crossTerm T.k2 cfU cfW cu0 cw0) cfW cw0
  set cπ1 := T.k2.ckE.commit (crossTerm T.k2 cfU1 cfW1 cu1 cw1) 0
  have hf1 := fold_complete T.k2 hf0 hcu1 (T.ch2 cfU1 cu1 cπ1) 0
  obtain ⟨w', u', hu', hxu'⟩ := hA n z0 zn U u π cfU cu0 cu1 cπ0 cπ1 (fun h => absurd h hn) hx0 hx1
  refine ⟨⟨_, T.fold1 U u π, w', u', _, T.fold2 cfU1 cu1 cπ1⟩, ?_, hUU, hu', hf1⟩
  simp [hn, hxu', Setup.augOut, cfU1]

/-- **IVC completeness**: for every `n` there is an accepting proof of `zₙ = Fⁿ(z₀)`. -/
theorem ivc_complete (hA : T.AugComplete) (hC : T.CFComplete) (z0 : S) :
    ∀ n, ∃ P : Proof T, T.Verify n z0 (T.step^[n] z0) P := by
  have good : ∀ n, ∃ P : Proof T, T.Good (n + 1) z0 (T.step^[n + 1] z0) P := by
    intro n
    induction n with
    | zero => exact prove_base T hA hC z0
    | succ n ih =>
      obtain ⟨P, hP⟩ := ih
      rw [Function.iterate_succ_apply' T.step (n + 1)]
      exact prove_succ T hA hC (n + 1) (by omega) z0 _ P hP
  intro n
  cases n with
  | zero =>
    obtain ⟨P, -⟩ := good 0
    exact ⟨P, by simp [Setup.Verify]⟩
  | succ n =>
    obtain ⟨P, hP⟩ := good n
    exact ⟨P, by simpa [Setup.Verify, Setup.Good] using hP⟩

end IVC
end Sonobe
