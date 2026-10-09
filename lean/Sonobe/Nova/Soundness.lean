import Sonobe.Nova.Fold

/-!
Algebraic soundness of the Nova fold (the deterministic core of the extractor).

If the folded instance `foldInstance ρ cmT U u` has a satisfying witness for three distinct
challenges `ρ`, with the commitments binding, then `U` and `u` themselves have satisfying witnesses.
Not covered: the forking step that produces three accepting transcripts, and the DL reduction
behind `¬ DLRel`.
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

/-- Two openings of `cm₀ + ρ cm₁` (distinct `ρ`) interpolate to openings of `cm₀`, `cm₁`;
by binding, any third opening lies on the same line. -/
theorem affine_extract {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {n : ℕ}
    (ck : PedersenKey F G n) (hno : ¬ ck.DLRel) {cm₀ cm₁ : G} {ρ₁ ρ₂ ρ₃ : F} (h12 : ρ₁ ≠ ρ₂)
    {a₁ a₂ a₃ : Fin n → F} {s₁ s₂ s₃ : F}
    (h₁ : ck.commit a₁ s₁ = cm₀ + ρ₁ • cm₁) (h₂ : ck.commit a₂ s₂ = cm₀ + ρ₂ • cm₁)
    (h₃ : ck.commit a₃ s₃ = cm₀ + ρ₃ • cm₁) :
    ∃ (p₀ p₁ : Fin n → F) (q₀ q₁ : F), ck.commit p₀ q₀ = cm₀ ∧ ck.commit p₁ q₁ = cm₁ ∧
      (a₁ = p₀ + ρ₁ • p₁ ∧ s₁ = q₀ + ρ₁ * q₁) ∧ (a₂ = p₀ + ρ₂ • p₁ ∧ s₂ = q₀ + ρ₂ * q₁) ∧
      (a₃ = p₀ + ρ₃ • p₁ ∧ s₃ = q₀ + ρ₃ * q₁) := by
  have hd : ρ₂ - ρ₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have hdd : (ρ₂ - ρ₁) * (ρ₂ - ρ₁)⁻¹ = 1 := mul_inv_cancel₀ hd
  set d := (ρ₂ - ρ₁)⁻¹
  set p₁ : Fin n → F := d • (a₂ - a₁)
  set q₁ : F := d * (s₂ - s₁)
  set p₀ : Fin n → F := a₁ - ρ₁ • p₁
  set q₀ : F := s₁ - ρ₁ * q₁
  have e₁ : a₁ = p₀ + ρ₁ • p₁ := by simp [p₀]
  have e₁' : s₁ = q₀ + ρ₁ * q₁ := by simp [q₀]
  have e₂ : a₂ = p₀ + ρ₂ • p₁ := by
    ext i; simp only [p₀, p₁, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (a₁ i - a₂ i) * hdd
  have e₂' : s₂ = q₀ + ρ₂ * q₁ := by
    simp only [q₀, q₁]; linear_combination (s₁ - s₂) * hdd
  have k₁ := h₁; rw [e₁, e₁', PedersenKey.commit_fold] at k₁
  have k₂ := h₂; rw [e₂, e₂', PedersenKey.commit_fold] at k₂
  have hc₁ : ck.commit p₁ q₁ = cm₁ := by
    refine smul_right_injective G hd ?_
    calc (ρ₂ - ρ₁) • ck.commit p₁ q₁
        = (ck.commit p₀ q₀ + ρ₂ • ck.commit p₁ q₁) - (ck.commit p₀ q₀ + ρ₁ • ck.commit p₁ q₁) := by
          rw [sub_smul]; abel
      _ = (cm₀ + ρ₂ • cm₁) - (cm₀ + ρ₁ • cm₁) := by rw [k₂, k₁]
      _ = (ρ₂ - ρ₁) • cm₁ := by rw [sub_smul]; abel
  have hc₀ : ck.commit p₀ q₀ = cm₀ := by
    rw [hc₁] at k₁; exact add_right_cancel k₁
  refine ⟨p₀, p₁, q₀, q₁, hc₀, hc₁, ⟨e₁, e₁'⟩, ⟨e₂, e₂'⟩, ?_⟩
  have := PedersenKey.binding ck hno (h₃.trans (by rw [← hc₀, ← hc₁, PedersenKey.commit_fold]) :
    ck.commit a₃ s₃ = ck.commit (p₀ + ρ₃ • p₁) (q₀ + ρ₃ * q₁))
  exact this

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G] {m l nw : ℕ}

/-- **Algebraic soundness of the Nova fold.** -/
theorem fold_sound (k : Key F G m l nw) (hE : ¬ k.ckE.DLRel) (hW : ¬ k.ckW.DLRel)
    (U : RunningInstance F G l) (u : IncomingInstance G F l) (cmT : G)
    {ρ₁ ρ₂ ρ₃ : F} (h12 : ρ₁ ≠ ρ₂) (h13 : ρ₁ ≠ ρ₃) (h23 : ρ₂ ≠ ρ₃)
    {W₁ W₂ W₃ : RunningWitness F m nw}
    (f₁ : k.Running (foldInstance ρ₁ cmT U u) W₁) (f₂ : k.Running (foldInstance ρ₂ cmT U u) W₂)
    (f₃ : k.Running (foldInstance ρ₃ cmT U u) W₃) :
    ∃ (W : RunningWitness F m nw) (w : IncomingWitness F nw), k.Running U W ∧ k.Incoming u w := by
  obtain ⟨r₁, oe₁, ow₁⟩ := f₁
  obtain ⟨r₂, oe₂, ow₂⟩ := f₂
  obtain ⟨r₃, oe₃, ow₃⟩ := f₃
  obtain ⟨pe₀, pe₁, qe₀, qe₁, ce₀, ce₁, ae₁, ae₂, ae₃⟩ :=
    affine_extract k.ckE hE h12 oe₁ oe₂ oe₃
  obtain ⟨pw₀, pw₁, qw₀, qw₁, cw₀, cw₁, aw₁, aw₂, aw₃⟩ :=
    affine_extract k.ckW hW h12 ow₁ ow₂ ow₃
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
  have s₁ := step ae₁.1 aw₁.1 r₁
  have s₂ := step ae₂.1 aw₂.1 r₂
  have s₃ := step ae₃.1 aw₃.1 r₃
  have q : ∀ i : Fin m, (k.r1cs.eval (zvec U.u U.x pw₀) - pe₀) i = 0 ∧
      (k.r1cs.eval (zvec U.u U.x pw₀ + zvec 1 u.x pw₁) - k.r1cs.eval (zvec U.u U.x pw₀)
        - k.r1cs.eval (zvec 1 u.x pw₁) - pe₁) i = 0 ∧ k.r1cs.eval (zvec 1 u.x pw₁) i = 0 :=
    fun i => quad_zero h12 h13 h23 (by linear_combination s₁ i) (by linear_combination s₂ i)
      (by linear_combination s₃ i)
  refine ⟨⟨pe₀, qe₀, pw₀, qw₀⟩, ⟨pw₁, qw₁⟩, ⟨?_, ce₀, cw₀⟩, ⟨?_, cw₁⟩⟩
  · funext i
    have := (q i).1
    simpa [sub_eq_zero] using this
  · funext i
    exact (q i).2.2
end Nova
end Sonobe
