import Sonobe.IVC.Soundness

/-!
**The run hypotheses are satisfiable, and not automatic, in a non-degenerate model.**

The model is a group of prime order, `F = G = ZMod 7`, with a Pedersen key of two generators, as in
the deployment. There

* binding at the openings of an honest rewinding holds (`honest`), while a rewinding that opens a
  commitment two ways is accepting and breaks it (`cheat_accepts`, `cheat_not_binds`);
* `HsAt` holds at equal inputs (`IVC.Setup.hsAt_self`), the case of an honest step.

`ExtractsAt` holds for the honest witness of an honest call (`LegoGroth16.ExtractsAt.of_valid`).
-/

namespace Sonobe
namespace NonDegenerate

open Nova R1CS

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

abbrev F := ZMod 7

/-- A key of two generators: `g₀ = 1`, `h = 3`. -/
def ck : PedersenKey F F 1 := ⟨![1], 3⟩

theorem commit_eq (v : Fin 1 → F) (r : F) : ck.commit v r = v 0 + 3 * r := by
  simp [PedersenKey.commit, ck, mul_comm]

/-- Shifting an opening by the relation keeps the commitment. -/
theorem commit_shift (v : Fin 1 → F) (r : F) : ck.commit (v + ![3]) (r - 1) = ck.commit v r := by
  simp only [commit_eq, Pi.add_apply]
  simp
  ring

/-- Two openings of the commitment `3`: binding fails at them. -/
theorem not_bindsAt : ¬ ck.BindsAt ![3] 0 ![0] 1 := by
  intro h
  have := congrFun (h (by simp only [commit_eq]; simp)).1 0
  revert this
  decide

/-- The trivial R1CS of one row, every assignment satisfies it. -/
def r1cs : R1CS F 1 1 1 := ⟨0, 0, 0⟩

def key : Key F F 1 1 1 := ⟨r1cs, ck, ck⟩

theorem eval_zero (z : Col 1 1 → F) : r1cs.eval z = 0 := by
  funext i; simp [R1CS.eval, r1cs]

theorem running_iff (U : RunningInstance F F 1) (W : RunningWitness F 1 1) :
    key.Running U W ↔ W.e = 0 ∧ ck.commit 0 W.rE = U.cmE ∧ ck.commit W.w W.rW = U.cmW := by
  simp only [Key.Running, RelaxedSat, key, eval_zero, PedersenKey.Opens]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, by rw [h1]; exact h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, by rw [h1]; exact h2, h3⟩

/-- An honest pair: the zero running instance, and an incoming instance opening `w = 1`. -/
def U : RunningInstance F F 1 := ⟨0, 0, 0, fun _ => 0⟩
def W : RunningWitness F 1 1 := ⟨0, 0, 0, 0⟩
def u : IncomingInstance F F 1 := ⟨ck.commit ![1] 0, ![0]⟩
def w : IncomingWitness F 1 := ⟨![1], 0⟩

theorem hU : key.Running U W := (running_iff U W).mpr ⟨rfl, by simp [commit_eq, U, W],
  by simp [commit_eq, U, W]⟩

theorem hu : key.Incoming u w := ⟨eval_zero _, rfl⟩

theorem h01 : (0 : F) ≠ 1 := by decide
theorem h02 : (0 : F) ≠ 2 := by decide
theorem h12 : (1 : F) ≠ 2 := by decide

/-- **The honest rewinding meets both hypotheses** at the challenges `0, 1, 2`. -/
theorem honest :
    let T := crossTerm key U W u w
    let r : Rewind F 1 1 := ⟨1, foldWitness 1 0 T W w, 2, foldWitness 2 0 T W w⟩
    r.Accepts key U u (key.ckE.commit T 0) 0 ∧ r.Binds key 0 (foldWitness 0 0 T W w) :=
  Rewind.honest key hU hu 0 h01 h02 h12

/-- A cheating rewinding: its third witness opens the folded `cm_W` with `w + 3`, `r_W - 1`. -/
def cheat : Rewind F 1 1 :=
  let T := crossTerm key U W u w
  let W₃ := foldWitness 2 0 T W w
  ⟨1, foldWitness 1 0 T W w, 2, ⟨W₃.e, W₃.rE, W₃.w + ![3], W₃.rW - 1⟩⟩

/-- It is accepting, ... -/
theorem cheat_accepts : cheat.Accepts key U u (key.ckE.commit (crossTerm key U W u w) 0) 0 := by
  obtain ⟨⟨-, -, -, h2, h3⟩, -⟩ := honest
  refine ⟨h01, h02, h12, h2, ?_⟩
  rw [running_iff] at h3 ⊢
  obtain ⟨e1, e2, e3⟩ := h3
  exact ⟨e1, e2, by simp only [cheat]; rw [commit_shift]; exact e3⟩

/-- ... but breaks binding: `Rewind.Binds` is not automatic. -/
theorem cheat_not_binds : ¬ cheat.Binds key 0 (foldWitness 0 0 (crossTerm key U W u w) W w) := by
  intro h
  have hb := h.2
  simp only [cheat] at hb
  set T := crossTerm key U W u w
  have hl : line (0 : F) 1 (foldWitness 0 0 T W w).w (foldWitness 1 0 T W w).w 2 =
      (foldWitness 2 0 T W w).w := by
    simp only [foldWitness, line, slope_line (M := Fin 1 → F) h01, icept_line (M := Fin 1 → F) h01]
  have hl' : line (0 : F) 1 (foldWitness 0 0 T W w).rW (foldWitness 1 0 T W w).rW 2 =
      (foldWitness 2 0 T W w).rW := by
    simp only [foldWitness, line, ← smul_eq_mul, slope_line (M := F) h01, icept_line (M := F) h01]
  rw [hl, hl'] at hb
  have := congrFun (hb (commit_shift _ _)).1 0
  have h3 : (3 : F) = 0 := by simpa using this
  exact absurd h3 (by decide)

end NonDegenerate

namespace IVC

variable {F1 G1 F2 G2 S C1 : Type*} [Field F1] [AddCommGroup G1] [Module F1 G1]
  [Field F2] [AddCommGroup G2] [Module F2 G2] {l2 : ℕ} (T : Setup F1 G1 F2 G2 S C1 l2)

/-- `HsAt` holds at equal inputs, as at an honest step, whatever the hash. -/
theorem Setup.hsAt_self (pp i : F1) (z0 zi : S) (U : RawRU F1 C1)
    (cfU : Nova.RunningInstance F2 G2 l2) : T.HsAt pp i z0 zi U cfU pp i z0 zi U cfU :=
  fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end IVC
end Sonobe
