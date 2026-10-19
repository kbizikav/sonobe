import Sonobe.Transcript.Sponge
import Sonobe.Transcript.PoseidonConstants

/-!
Poseidon permutation and its R1CS gadget, the transcript of the deployment
(`PoseidonSponge` / `PoseidonSpongeVar` via `crates/primitives/src/transcripts/poseidon/sponge.rs`),
modelled on `ark-crypto-primitives` 0.6.0: `PoseidonSponge::permute` (`sponge/poseidon/mod.rs:98`)
and `PoseidonSpongeVar::permute` (`sponge/poseidon/constraints.rs:83`). Ported from zERC20's
`lean/Zerc20/{Poseidon,Ark}.lean`, over any field.

* `Params.perm` is the standard permutation; `circom5` its circomlib constants for `t = 5`
  (`POSEIDON4`: rate 4, capacity 1, 8 full and 60 partial rounds, `α = 5`), which are those of
  BN254's scalar field.
* `Gadget.permute` is the gadget: the constraints it emits and the state it returns. arkworks folds
  constants (an operation on constants emits nothing), so `FpVar` keeps the `Constant`/`Var` split
  and the same constraints remain. `permRel_iff`: the gadget's constraints hold exactly at the
  permutation's output.
-/

namespace Sonobe
namespace Poseidon

open Matrix

variable {F : Type*} [Field F] {t : ℕ}

/-- arkworks' `PoseidonConfig` with `alpha = 5` and capacity 1, for a state of `t` lanes. -/
structure Params (F : Type*) (t : ℕ) where
  fullRounds : ℕ
  partialRounds : ℕ
  /-- `ark[i][j]`: the constant added to lane `j` in round `i`. -/
  ark : ℕ → Fin t → F
  /-- `mds[i][j]`: `apply_mds` sets lane `i` to the sum of `mds[i][j]·state[j]`. -/
  mds : Matrix (Fin t) (Fin t) F

/-- `apply_s_box`: `x⁵` on every lane in a full round, on lane 0 alone in a partial round. -/
def sbox (full : Bool) (s : Fin t → F) : Fin t → F :=
  fun i => if full || i.val = 0 then s i ^ 5 else s i

namespace Params

/-- `permute` runs `fullRounds / 2` full rounds, then the partial rounds, then the other full
rounds. -/
def isFull (p : Params F t) (i : ℕ) : Bool :=
  i < p.fullRounds / 2 || p.fullRounds / 2 + p.partialRounds ≤ i

/-- Round `i` of `permute`: `apply_ark`, `apply_s_box`, `apply_mds`. -/
def round (p : Params F t) (i : ℕ) (s : Fin t → F) : Fin t → F :=
  p.mds *ᵥ sbox (p.isFull i) (s + p.ark i)

/-- The state after the first `k` rounds. -/
def rounds (p : Params F t) (k : ℕ) (s : Fin t → F) : Fin t → F :=
  (List.range k).foldl (fun s i => p.round i s) s

/-- `PoseidonSponge::permute`. Its three loops (full, partial, full rounds) are one loop over all
rounds here, with `isFull` telling the kinds apart. -/
def perm (p : Params F t) (s : Fin t → F) : Fin t → F :=
  p.rounds (p.fullRounds + p.partialRounds) s

theorem rounds_succ (p : Params F t) (k : ℕ) (s : Fin t → F) :
    p.rounds (k + 1) s = p.round k (p.rounds k s) := by
  simp [rounds, List.range_succ, List.foldl_append]

end Params

/-- A matrix given row by row; entries past the lists' ends are 0. -/
def castMat (m : List (List ℕ)) : Matrix (Fin t) (Fin t) F :=
  Matrix.of fun i j => ((m.getD i []).getD j 0 : F)

/-- Standard parameters from the generated lists: 8 full rounds, `ark` flat with `t` constants per
round, `mds` row by row. -/
def ofLists (partialRounds : ℕ) (ark : List ℕ) (mds : List (List ℕ)) : Params F t where
  fullRounds := 8
  partialRounds := partialRounds
  ark i j := (ark.getD (i * t + j) 0 : F)
  mds := castMat mds

/-- circomlib's standard parameters for `t = 5`, zERC20's `POSEIDON4`. The constants are elements
of BN254's scalar field, so this is that config when `F` is that field. -/
def circom5 : Params F 5 :=
  ofLists PoseidonConstants.T5.partialRounds PoseidonConstants.T5.ark PoseidonConstants.T5.mds

/-! ### The gadget (`PoseidonSpongeVar::permute`) -/

/-- `FpVar<F>`: a constant, or a variable whose linear combination has value `x`. -/
inductive FpVar (F : Type*)
  | const (c : F)
  | var (x : F)

namespace FpVar

def val : FpVar F → F
  | const c => c
  | var x => x

/-- `FpVar + FpVar`, a linear combination. -/
def add : FpVar F → FpVar F → FpVar F
  | const a, const b => const (a + b)
  | const c, var v | var v, const c => var (v + c)
  | var x, var y => var (x + y)

theorem add_val (a b : FpVar F) : (add a b).val = a.val + b.val := by
  cases a <;> cases b <;> simp [add, val, add_comm]

/-- `FpVar * FpVar`; `z` is the product's witness when both sides are variables. -/
def mul : FpVar F → FpVar F → F → FpVar F
  | const a, const b, _ => const (a * b)
  | const c, var v, _ | var v, const c, _ => var (v * c)
  | var _, var _, z => var z

/-- The constraint `a · b = z` emitted between two variables. -/
def mul.Rel : FpVar F → FpVar F → F → Prop
  | var x, var y, z => x * y = z
  | _, _, _ => True

theorem mul.sound {a b : FpVar F} {z : F} (h : mul.Rel a b z) :
    (mul a b z).val = a.val * b.val := by
  cases a <;> cases b <;> simp_all [mul, mul.Rel, val, mul_comm]

theorem mul.complete (a b : FpVar F) : mul.Rel a b (a.val * b.val) := by
  cases a <;> cases b <;> simp [mul.Rel, val]

end FpVar

namespace Gadget

open FpVar

open Classical in
/-- `FpVar * F`: a zero constant gives `FpVar::zero()`; any other constant folds into the linear
combination, with no constraint. -/
noncomputable def mulConst (x : FpVar F) (c : F) : FpVar F := if c = 0 then .const 0 else x.mul (.const c) 0

theorem mulConst_val (x : FpVar F) (c : F) : (mulConst x c).val = x.val * c := by
  unfold mulConst
  split_ifs with h
  · simp [FpVar.val, h]
  · cases x <;> simp [FpVar.mul, FpVar.val]

/-- `FpVar::pow_by_constant(&[5])`: from `res = one()`, over the bits `1, 0, 1` of 5, `square`,
then `*= self` on a set bit. The first two steps fold, since `one()` is a constant; each later
product of two variables allocates its witness from `w`. -/
def pow5 (x : FpVar F) (w : F × F × F) : Prop × FpVar F :=
  let one := FpVar.const (1 : F)
  let r₁ := one.mul one 0
  let r₂ := r₁.mul x 0
  let r₃ := r₂.mul r₂ w.1
  let r₄ := r₃.mul r₃ w.2.1
  let r₅ := r₄.mul x w.2.2
  (mul.Rel one one 0 ∧ mul.Rel r₁ x 0 ∧ mul.Rel r₂ r₂ w.1 ∧ mul.Rel r₃ r₃ w.2.1 ∧
    mul.Rel r₄ x w.2.2, r₅)

/-- The witnesses `pow_by_constant(&[5])` assigns on a value `v`: `v²`, `v⁴`, `v⁵`. -/
def pow5.wit (v : F) : F × F × F := (v * v, v * v * (v * v), v * v * (v * v) * v)

theorem pow5.sound {x : FpVar F} {w : F × F × F} (h : (pow5 x w).1) :
    (pow5 x w).2.val = x.val ^ 5 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  simp only [pow5] at *
  rw [mul.sound h₅, mul.sound h₄, mul.sound h₃, mul.sound h₂, mul.sound h₁]
  simp only [FpVar.val]
  ring

theorem pow5.complete (x : FpVar F) : (pow5 x (pow5.wit x.val)).1 := by
  cases x <;> simp [pow5, pow5.wit, FpVar.mul, mul.Rel, FpVar.val]

/-- `apply_s_box`: `pow_by_constant(&[5])` on every lane in a full round, on lane 0 in a partial
round, with `w j` the witnesses of lane `j`. -/
def applySbox [NeZero t] (full : Bool) (s : Fin t → FpVar F) (w : Fin t → F × F × F) :
    Prop × (Fin t → FpVar F) :=
  if full then (∀ j, (pow5 (s j) (w j)).1, fun j => (pow5 (s j) (w j)).2)
  else ((pow5 (s 0) (w 0)).1, Function.update s 0 (pow5 (s 0) (w 0)).2)

/-- `apply_ark`: `state[j] += ark[i][j]`, a linear combination. -/
def applyArk (p : Params F t) (i : ℕ) (s : Fin t → FpVar F) : Fin t → FpVar F :=
  fun j => (s j).add (.const (p.ark i j))

/-- `apply_mds`: lane `i` is `cur += state[j] * mds[i][j]` over `j`, from `cur = zero()`; all
linear combinations. -/
noncomputable def applyMds (p : Params F t) (s : Fin t → FpVar F) : Fin t → FpVar F := fun i =>
  (List.finRange t).foldl (fun cur j => cur.add (mulConst (s j) (p.mds i j))) (.const 0)

/-- Round `i` of `permute`, with `w` the S-box witnesses of its lanes. -/
noncomputable def round [NeZero t] (p : Params F t) (i : ℕ) (w : Fin t → F × F × F) (s : Fin t → FpVar F) :
    Prop × (Fin t → FpVar F) :=
  let b := applySbox (p.isFull i) (applyArk p i s) w
  (b.1, applyMds p b.2)

/-- The constraints of the first `k` rounds of `permute` and the state after them, with `w i` the
S-box witnesses of round `i`. -/
noncomputable def rounds [NeZero t] (p : Params F t) (w : ℕ → Fin t → F × F × F) (k : ℕ)
    (s : Fin t → FpVar F) : Prop × (Fin t → FpVar F) :=
  (List.range k).foldl (fun acc i => (acc.1 ∧ (round p i (w i) acc.2).1, (round p i (w i) acc.2).2))
    (True, s)

/-- `PoseidonSpongeVar::permute`. -/
noncomputable def permute [NeZero t] (p : Params F t) (w : ℕ → Fin t → F × F × F) (s : Fin t → FpVar F) :
    Prop × (Fin t → FpVar F) :=
  rounds p w (p.fullRounds + p.partialRounds) s

/-- The values of a state. -/
def vals (s : Fin t → FpVar F) : Fin t → F := fun j => (s j).val

theorem applyArk_vals (p : Params F t) (i : ℕ) (s : Fin t → FpVar F) :
    vals (applyArk p i s) = vals s + p.ark i :=
  funext fun _ => FpVar.add_val _ _

theorem foldl_mulConst_val (s : Fin t → FpVar F) (m : Fin t → F) (l : List (Fin t))
    (init : FpVar F) :
    (l.foldl (fun cur j => cur.add (mulConst (s j) (m j))) init).val =
      init.val + (l.map fun j => (s j).val * m j).sum := by
  induction l generalizing init with
  | nil => simp
  | cons j l ih => simp [ih, FpVar.add_val, mulConst_val, add_assoc]

theorem applyMds_vals (p : Params F t) (s : Fin t → FpVar F) :
    vals (applyMds p s) = p.mds *ᵥ vals s := by
  funext i
  simp only [vals, applyMds, foldl_mulConst_val, mulVec, dotProduct, Fin.sum_univ_def]
  simp [FpVar.val, mul_comm]

variable [NeZero t]

theorem applySbox.sound {full : Bool} {s : Fin t → FpVar F} {w : Fin t → F × F × F}
    (h : (applySbox full s w).1) :
    vals (applySbox full s w).2 = sbox full (vals s) := by
  funext j
  cases full
  · simp only [applySbox, Bool.false_eq_true, if_false] at h ⊢
    by_cases hj : j = 0
    · subst hj; simp [vals, sbox, pow5.sound h]
    · simp [vals, sbox, hj, Fin.val_eq_zero_iff]
  · simp only [applySbox, if_true] at h ⊢
    simp [vals, sbox, pow5.sound (h j)]

theorem applySbox.complete (full : Bool) (s : Fin t → FpVar F) :
    (applySbox full s fun j => pow5.wit (s j).val).1 := by
  cases full
  · exact pow5.complete _
  · exact fun j => pow5.complete _

theorem round.sound {p : Params F t} {i : ℕ} {w : Fin t → F × F × F} {s : Fin t → FpVar F}
    (h : (round p i w s).1) : vals (round p i w s).2 = p.round i (vals s) := by
  simp only [round] at h ⊢
  rw [applyMds_vals, applySbox.sound h, applyArk_vals]
  rfl

theorem rounds_succ (p : Params F t) (w : ℕ → Fin t → F × F × F) (k : ℕ) (s : Fin t → FpVar F) :
    rounds p w (k + 1) s = ((rounds p w k s).1 ∧ (round p k (w k) (rounds p w k s).2).1,
      (round p k (w k) (rounds p w k s).2).2) := by
  simp [rounds, List.range_succ, List.foldl_append]

theorem rounds.sound {p : Params F t} {w : ℕ → Fin t → F × F × F} {k : ℕ}
    {s : Fin t → FpVar F} (h : (rounds p w k s).1) :
    vals (rounds p w k s).2 = p.rounds k (vals s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rounds_succ] at h ⊢
    rw [round.sound h.2, ih h.1, p.rounds_succ]

/-- The S-box witnesses of every round, from the values `v` of the initial state. -/
def wit (p : Params F t) (v : Fin t → F) : ℕ → Fin t → F × F × F :=
  fun i j => pow5.wit ((p.rounds i v + p.ark i) j)

theorem rounds.complete (p : Params F t) (k : ℕ) (s : Fin t → FpVar F) :
    (rounds p (wit p (vals s)) k s).1 := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [rounds_succ]
    refine ⟨ih, ?_⟩
    have hv := rounds.sound ih
    have : wit p (vals s) k =
        fun j => pow5.wit ((applyArk p k (rounds p (wit p (vals s)) k s).2) j).val := by
      funext j
      rw [show ((applyArk p k _) j).val = vals (applyArk p k _) j from rfl, applyArk_vals, hv]
      rfl
    rw [this]
    exact applySbox.complete _ _

end Gadget

/-! ### Bind -/

variable [NeZero t] (p : Params F t)

/-- The permutation gadget relates `inp` to `out`: some state with values `inp` and some S-box
witnesses satisfy its constraints, and its output has values `out`. -/
def PermRel (inp out : Fin t → F) : Prop :=
  ∃ (s : Fin t → FpVar F) (w : ℕ → Fin t → F × F × F), Gadget.vals s = inp ∧
    (Gadget.permute p w s).1 ∧ Gadget.vals (Gadget.permute p w s).2 = out

/-- **Bind**: the permutation gadget's constraints hold exactly at `perm inp` (no
under-constrained output, no unsatisfiable honest run). -/
theorem permRel_iff (inp out : Fin t → F) : PermRel p inp out ↔ out = p.perm inp := by
  constructor
  · rintro ⟨s, w, rfl, h, rfl⟩
    exact Gadget.rounds.sound h
  · rintro rfl
    have hc := Gadget.rounds.complete p (p.fullRounds + p.partialRounds) (fun j => .var (inp j))
    exact ⟨fun j => .var (inp j), Gadget.wit p inp, rfl, hc, Gadget.rounds.sound hc⟩

/-- `PoseidonSponge`: capacity 1, rate `t - 1` (`PoseidonConfig::new(.., rate, 1)`). -/
def Params.cfg : SpongeCfg F := ⟨t, 1, t - 1, p.perm⟩

/-- **Sponge bind.** A circuit sponge whose every permutation call is only constrained by the
`PoseidonSpongeVar::permute` constraints behaves exactly like the specification sponge: its outputs
are determined by the absorbed inputs. -/
theorem circuit_sponge_bind (π' : (Fin t → F) → (Fin t → F)) (h : ∀ s, PermRel p s (π' s)) :
    ({ p.cfg with perm := π' } : SpongeCfg F) = p.cfg := by
  have : π' = p.perm := funext fun s => (permRel_iff p s _).mp (h s)
  simp [Params.cfg, this]

end Poseidon
end Sonobe
