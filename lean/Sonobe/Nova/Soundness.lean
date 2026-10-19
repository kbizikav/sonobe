import Sonobe.Nova.Fold

/-!
Algebraic soundness of the Nova fold (the deterministic core of the extractor).

If the folded instance `foldInstance ρ cmT U u` has satisfying witnesses for three distinct
challenges `ρ`, and binding holds at the third witness's openings, then `U` and `u` have the
satisfying witnesses `extract` interpolates from the first two. The other two witnesses are what
rewinding the prover yields (`Rewind`); binding is assumed at the values the rewinding produced
(`Rewind.Binds`), and a break of it is a discrete-log relation computed from them.
-/

namespace Sonobe
namespace Nova

open R1CS

/-- Three distinct points determine a quadratic. -/
theorem quad_zero {F : Type*} [Field F] {ρ₁ ρ₂ ρ₃ a b c : F}
    (h12 : ρ₁ ≠ ρ₂) (h13 : ρ₁ ≠ ρ₃) (h23 : ρ₂ ≠ ρ₃)
    (e₁ : a + b * ρ₁ + c * ρ₁ ^ 2 = 0) (e₂ : a + b * ρ₂ + c * ρ₂ ^ 2 = 0)
    (e₃ : a + b * ρ₃ + c * ρ₃ ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have k12 : b + c * (ρ₁ + ρ₂) = 0 := by
    have : (ρ₁ - ρ₂) * (b + c * (ρ₁ + ρ₂)) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h12)
  have k13 : b + c * (ρ₁ + ρ₃) = 0 := by
    have : (ρ₁ - ρ₃) * (b + c * (ρ₁ + ρ₃)) = 0 := by linear_combination e₁ - e₃
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h13)
  have hc : c = 0 := by
    have : (ρ₂ - ρ₃) * c = 0 := by linear_combination k12 - k13
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h23)
  subst hc
  have hb : b = 0 := by simpa using k12
  subst hb
  exact ⟨by simpa using e₁, rfl, rfl⟩

/-! ### Interpolation -/

section Line

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Slope of the line through `(ρ₁, a₁)` and `(ρ₂, a₂)`. -/
def slope (ρ₁ ρ₂ : F) (a₁ a₂ : M) : M := (ρ₂ - ρ₁)⁻¹ • (a₂ - a₁)

/-- Its value at `0`. -/
def icept (ρ₁ ρ₂ : F) (a₁ a₂ : M) : M := a₁ - ρ₁ • slope ρ₁ ρ₂ a₁ a₂

/-- Its value at `ρ`. -/
def line (ρ₁ ρ₂ : F) (a₁ a₂ : M) (ρ : F) : M := icept ρ₁ ρ₂ a₁ a₂ + ρ • slope ρ₁ ρ₂ a₁ a₂

theorem line_fst (ρ₁ ρ₂ : F) (a₁ a₂ : M) : a₁ = icept ρ₁ ρ₂ a₁ a₂ + ρ₁ • slope ρ₁ ρ₂ a₁ a₂ := by
  simp [icept]

theorem line_snd {ρ₁ ρ₂ : F} (h12 : ρ₁ ≠ ρ₂) (a₁ a₂ : M) :
    a₂ = icept ρ₁ ρ₂ a₁ a₂ + ρ₂ • slope ρ₁ ρ₂ a₁ a₂ := by
  have hd : ρ₂ - ρ₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have h : ρ₂ • slope ρ₁ ρ₂ a₁ a₂ - ρ₁ • slope ρ₁ ρ₂ a₁ a₂ = a₂ - a₁ := by
    rw [← sub_smul, slope, smul_smul, mul_inv_cancel₀ hd, one_smul]
  unfold icept
  calc a₂ = a₁ + (a₂ - a₁) := by abel
    _ = a₁ - ρ₁ • slope ρ₁ ρ₂ a₁ a₂ + ρ₂ • slope ρ₁ ρ₂ a₁ a₂ := by rw [← h]; abel

/-- Points on a line interpolate back to it. -/
theorem slope_line {ρ₁ ρ₂ : F} (h12 : ρ₁ ≠ ρ₂) (p₀ p₁ : M) :
    slope ρ₁ ρ₂ (p₀ + ρ₁ • p₁) (p₀ + ρ₂ • p₁) = p₁ := by
  have hd : ρ₂ - ρ₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  simp only [slope, add_sub_add_left_eq_sub, ← sub_smul, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem icept_line {ρ₁ ρ₂ : F} (h12 : ρ₁ ≠ ρ₂) (p₀ p₁ : M) :
    icept ρ₁ ρ₂ (p₀ + ρ₁ • p₁) (p₀ + ρ₂ • p₁) = p₀ := by
  simp [icept, slope_line h12]

end Line

/-- Two openings of `cm₀ + ρ cm₁` (distinct `ρ`) interpolate to openings of `cm₀`, `cm₁`; a third
opening lies on the same line if binding holds at it (`hb`). -/
theorem affine_extract {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
    (ck : PedersenKey F G n) {cm₀ cm₁ : G} {ρ₁ ρ₂ ρ₃ : F} (h12 : ρ₁ ≠ ρ₂)
    {a₁ a₂ a₃ : Fin n → F} {s₁ s₂ s₃ : F}
    (h₁ : ck.commit a₁ s₁ = cm₀ + ρ₁ • cm₁) (h₂ : ck.commit a₂ s₂ = cm₀ + ρ₂ • cm₁)
    (h₃ : ck.commit a₃ s₃ = cm₀ + ρ₃ • cm₁)
    (hb : ck.BindsAt a₃ s₃ (line ρ₁ ρ₂ a₁ a₂ ρ₃) (line ρ₁ ρ₂ s₁ s₂ ρ₃)) :
    ck.commit (icept ρ₁ ρ₂ a₁ a₂) (icept ρ₁ ρ₂ s₁ s₂) = cm₀ ∧
      ck.commit (slope ρ₁ ρ₂ a₁ a₂) (slope ρ₁ ρ₂ s₁ s₂) = cm₁ ∧
      a₃ = line ρ₁ ρ₂ a₁ a₂ ρ₃ ∧ s₃ = line ρ₁ ρ₂ s₁ s₂ ρ₃ := by
  have hd : ρ₂ - ρ₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  set p₀ := icept ρ₁ ρ₂ a₁ a₂
  set p₁ := slope ρ₁ ρ₂ a₁ a₂
  set q₀ := icept ρ₁ ρ₂ s₁ s₂
  set q₁ := slope ρ₁ ρ₂ s₁ s₂
  have k₁ := h₁; rw [line_fst ρ₁ ρ₂ a₁ a₂, line_fst ρ₁ ρ₂ s₁ s₂, smul_eq_mul,
    PedersenKey.commit_fold] at k₁
  have k₂ := h₂; rw [line_snd h12 a₁ a₂, line_snd h12 s₁ s₂, smul_eq_mul,
    PedersenKey.commit_fold] at k₂
  have hc₁ : ck.commit p₁ q₁ = cm₁ := by
    refine smul_right_injective G hd ?_
    calc (ρ₂ - ρ₁) • ck.commit p₁ q₁
        = (ck.commit p₀ q₀ + ρ₂ • ck.commit p₁ q₁) - (ck.commit p₀ q₀ + ρ₁ • ck.commit p₁ q₁) := by
          rw [sub_smul]; abel
      _ = (cm₀ + ρ₂ • cm₁) - (cm₀ + ρ₁ • cm₁) := by rw [k₂, k₁]
      _ = (ρ₂ - ρ₁) • cm₁ := by rw [sub_smul]; abel
  have hc₀ : ck.commit p₀ q₀ = cm₀ := by
    rw [hc₁] at k₁; exact add_right_cancel k₁
  refine ⟨hc₀, hc₁, hb ?_⟩
  rw [h₃, line, line, smul_eq_mul, PedersenKey.commit_fold, hc₀, hc₁]

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {m l nw : ℕ}

/-- The witnesses of `U` and `u` interpolated from accepting witnesses `W₁`, `W₂` of the folds at
`ρ₁ ≠ ρ₂`: the values at `0` and the slopes of the lines through their openings. -/
def extract (ρ₁ ρ₂ : F) (W₁ W₂ : RunningWitness F m nw) :
    RunningWitness F m nw × IncomingWitness F nw :=
  (⟨icept ρ₁ ρ₂ W₁.e W₂.e, icept ρ₁ ρ₂ W₁.rE W₂.rE, icept ρ₁ ρ₂ W₁.w W₂.w,
    icept ρ₁ ρ₂ W₁.rW W₂.rW⟩, ⟨slope ρ₁ ρ₂ W₁.w W₂.w, slope ρ₁ ρ₂ W₁.rW W₂.rW⟩)

/-- Binding at a third witness `W₃` (challenge `ρ₃`): its openings of `cm_E` and `cm_W` are not
different from the ones interpolated from `W₁` and `W₂`. -/
def Binds3 (k : Key F G m l nw) (ρ₁ ρ₂ ρ₃ : F) (W₁ W₂ W₃ : RunningWitness F m nw) : Prop :=
  k.ckE.BindsAt W₃.e W₃.rE (line ρ₁ ρ₂ W₁.e W₂.e ρ₃) (line ρ₁ ρ₂ W₁.rE W₂.rE ρ₃) ∧
    k.ckW.BindsAt W₃.w W₃.rW (line ρ₁ ρ₂ W₁.w W₂.w ρ₃) (line ρ₁ ρ₂ W₁.rW W₂.rW ρ₃)

/-- **Algebraic soundness of the Nova fold.** Accepting witnesses of the folded instance at three
distinct challenges, with binding at the third, give witnesses of `U` and `u`: those `extract`
interpolates from the first two. -/
theorem fold_sound (k : Key F G m l nw) (U : RunningInstance F G l) (u : IncomingInstance G F l)
    (cmT : G) {ρ₁ ρ₂ ρ₃ : F} (h12 : ρ₁ ≠ ρ₂) (h13 : ρ₁ ≠ ρ₃) (h23 : ρ₂ ≠ ρ₃)
    {W₁ W₂ W₃ : RunningWitness F m nw}
    (f₁ : k.Running (foldInstance ρ₁ cmT U u) W₁) (f₂ : k.Running (foldInstance ρ₂ cmT U u) W₂)
    (f₃ : k.Running (foldInstance ρ₃ cmT U u) W₃) (hb : Binds3 k ρ₁ ρ₂ ρ₃ W₁ W₂ W₃) :
    k.Running U (extract ρ₁ ρ₂ W₁ W₂).1 ∧ k.Incoming u (extract ρ₁ ρ₂ W₁ W₂).2 := by
  obtain ⟨r₁, oe₁, ow₁⟩ := f₁
  obtain ⟨r₂, oe₂, ow₂⟩ := f₂
  obtain ⟨r₃, oe₃, ow₃⟩ := f₃
  obtain ⟨ce₀, ce₁, ae₃, -⟩ := affine_extract k.ckE h12 oe₁ oe₂ oe₃ hb.1
  obtain ⟨cw₀, cw₁, aw₃, -⟩ := affine_extract k.ckW h12 ow₁ ow₂ ow₃ hb.2
  set pe₀ := icept ρ₁ ρ₂ W₁.e W₂.e
  set pe₁ := slope ρ₁ ρ₂ W₁.e W₂.e
  set pw₀ := icept ρ₁ ρ₂ W₁.w W₂.w
  set pw₁ := slope ρ₁ ρ₂ W₁.w W₂.w
  have ae₁ : W₁.e = pe₀ + ρ₁ • pe₁ := line_fst _ _ _ _
  have ae₂ : W₂.e = pe₀ + ρ₂ • pe₁ := line_snd h12 _ _
  have aw₁ : W₁.w = pw₀ + ρ₁ • pw₁ := line_fst _ _ _ _
  have aw₂ : W₂.w = pw₀ + ρ₂ • pw₁ := line_snd h12 _ _
  -- relaxed R1CS on the three folded points, rewritten along the interpolation
  have step : ∀ {ρ : F} {W' : RunningWitness F m nw}, W'.e = pe₀ + ρ • pe₁ → W'.w = pw₀ + ρ • pw₁ →
      k.r1cs.RelaxedSat (U.u + ρ) (U.x + ρ • u.x) W'.w W'.e →
      ∀ i, (k.r1cs.eval (zvec U.u U.x pw₀) - pe₀) i + ρ * (k.r1cs.eval (zvec U.u U.x pw₀ + zvec 1 u.x pw₁)
        - k.r1cs.eval (zvec U.u U.x pw₀) - k.r1cs.eval (zvec 1 u.x pw₁) - pe₁) i
        + ρ ^ 2 * k.r1cs.eval (zvec 1 u.x pw₁) i = 0 := by
    intro ρ W' he hw hs i
    rw [RelaxedSat, hw, he, zvec_fold, R1CS.eval_fold] at hs
    have := congrFun hs i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this ⊢
    linear_combination this
  have s₁ := step ae₁ aw₁ r₁
  have s₂ := step ae₂ aw₂ r₂
  have s₃ := step ae₃ aw₃ r₃
  have q : ∀ i : Fin m, (k.r1cs.eval (zvec U.u U.x pw₀) - pe₀) i = 0 ∧
      (k.r1cs.eval (zvec U.u U.x pw₀ + zvec 1 u.x pw₁) - k.r1cs.eval (zvec U.u U.x pw₀)
        - k.r1cs.eval (zvec 1 u.x pw₁) - pe₁) i = 0 ∧ k.r1cs.eval (zvec 1 u.x pw₁) i = 0 :=
    fun i => quad_zero h12 h13 h23 (by linear_combination s₁ i) (by linear_combination s₂ i)
      (by linear_combination s₃ i)
  refine ⟨⟨?_, ce₀, cw₀⟩, ⟨?_, cw₁⟩⟩
  · funext i
    have := (q i).1
    simpa [sub_eq_zero] using this
  · funext i
    exact (q i).2.2

/-! ### Rewinding -/

/-- Two more accepting witnesses of a fold whose challenge was `ρ`, at challenges `ρ₂`, `ρ₃`: what
rewinding the prover to the challenge yields (forking lemma). -/
structure Rewind (F : Type*) (m nw : ℕ) where
  ρ₂ : F
  W₂ : RunningWitness F m nw
  ρ₃ : F
  W₃ : RunningWitness F m nw

namespace Rewind

/-- The rewound witnesses are accepting, at challenges distinct from each other and from `ρ`. This
is what the forking lemma provides. -/
def Accepts (k : Key F G m l nw) (U : RunningInstance F G l) (u : IncomingInstance G F l) (cmT : G)
    (ρ : F) (r : Rewind F m nw) : Prop :=
  ρ ≠ r.ρ₂ ∧ ρ ≠ r.ρ₃ ∧ r.ρ₂ ≠ r.ρ₃ ∧ k.Running (foldInstance r.ρ₂ cmT U u) r.W₂ ∧
    k.Running (foldInstance r.ρ₃ cmT U u) r.W₃

/-- No rewound witness breaks binding: `W₃`'s openings are those interpolated from `W` and `W₂`.
A break is a discrete-log relation computed from them (`PedersenKey.dlRel_of_not_bindsAt`). -/
def Binds (k : Key F G m l nw) (ρ : F) (W : RunningWitness F m nw) (r : Rewind F m nw) : Prop :=
  Binds3 k ρ r.ρ₂ r.ρ₃ W r.W₂ r.W₃

/-- The extracted witnesses of `U` and `u`. -/
def extract (ρ : F) (W : RunningWitness F m nw) (r : Rewind F m nw) :
    RunningWitness F m nw × IncomingWitness F nw :=
  Nova.extract ρ r.ρ₂ W r.W₂

/-- **Fold extraction from a rewinding.** -/
theorem sound (k : Key F G m l nw) {U : RunningInstance F G l} {u : IncomingInstance G F l}
    {cmT : G} {ρ : F} {W : RunningWitness F m nw} {r : Rewind F m nw}
    (hW : k.Running (foldInstance ρ cmT U u) W) (ha : r.Accepts k U u cmT ρ)
    (hb : r.Binds k ρ W) :
    k.Running U (r.extract ρ W).1 ∧ k.Incoming u (r.extract ρ W).2 := by
  obtain ⟨h12, h13, h23, f₂, f₃⟩ := ha
  exact fold_sound k U u cmT h12 h13 h23 hW f₂ f₃ hb

/-- **An honest rewinding meets both hypotheses**: folding satisfying `(W, w)` at three distinct
challenges gives accepting witnesses, and they lie on one line, so binding holds at the third. -/
theorem honest (k : Key F G m l nw) {U : RunningInstance F G l} {W : RunningWitness F m nw}
    {u : IncomingInstance G F l} {w : IncomingWitness F nw} (hU : k.Running U W)
    (hu : k.Incoming u w) (rT : F) {ρ ρ₂ ρ₃ : F} (h12 : ρ ≠ ρ₂) (h13 : ρ ≠ ρ₃) (h23 : ρ₂ ≠ ρ₃) :
    let T := crossTerm k U W u w
    let r : Rewind F m nw := ⟨ρ₂, foldWitness ρ₂ rT T W w, ρ₃, foldWitness ρ₃ rT T W w⟩
    r.Accepts k U u (k.ckE.commit T rT) ρ ∧ r.Binds k ρ (foldWitness ρ rT T W w) := by
  intro T r
  refine ⟨⟨h12, h13, h23, fold_complete k hU hu ρ₂ rT, fold_complete k hU hu ρ₃ rT⟩, ?_, ?_⟩
  · simp only [r, foldWitness, line, ← smul_eq_mul, slope_line (M := Fin m → F) h12,
      icept_line (M := Fin m → F) h12, slope_line (M := F) h12, icept_line (M := F) h12]
    exact PedersenKey.bindsAt_self _ _ _
  · simp only [r, foldWitness, line, ← smul_eq_mul, slope_line (M := Fin nw → F) h12,
      icept_line (M := Fin nw → F) h12, slope_line (M := F) h12, icept_line (M := F) h12]
    exact PedersenKey.bindsAt_self _ _ _

end Rewind

end Nova
end Sonobe
