import Sonobe.Nova.Fold

/-!
Fiat-Shamir input of the Nova fold, modelled on
`transcript.add(U).add(u).add(cm_t).challenge_bits(B)` (nova/algorithms/verifier.rs:25) and the
`Absorbable` impls (nova/instances/mod.rs:48, :85).

Absorption order: `U = (u, x, cm_e, cm_w)`, `u = (x, cm_w)`, then `cm_t`. Vectors are absorbed
without a length prefix (algebra/field/mod.rs, transcripts/absorbable.rs), so injectivity needs the
shape `l` fixed — it is, through `pp_hash`, which seeds the transcript.

`encG` abstracts how a point becomes transcript-field elements (affine `(x, y)`, infinity ↦ `(0,0)`,
limb-split when the base field differs). Hypotheses: fixed length, injective.
-/

namespace Sonobe
namespace Nova

variable {F G : Type*} {l : ℕ}

structure Enc (G F : Type*) where
  enc : G → List F
  len : ℕ
  enc_len : ∀ g, (enc g).length = len
  enc_inj : Function.Injective enc

variable (E : Enc G F)

def encRunning (U : RunningInstance F G l) : List F :=
  [U.u] ++ List.ofFn U.x ++ E.enc U.cmE ++ E.enc U.cmW

def encIncoming (u : IncomingInstance G F l) : List F :=
  List.ofFn u.x ++ E.enc u.cmW

/-- Everything `ρ` is derived from. -/
def chalInput (U : RunningInstance F G l) (u : IncomingInstance G F l) (cmT : G) : List F :=
  encRunning E U ++ encIncoming E u ++ E.enc cmT

theorem encRunning_length (U : RunningInstance F G l) : (encRunning E U).length = 1 + l + 2 * E.len := by
  simp [encRunning, E.enc_len]; ring

theorem encIncoming_length (u : IncomingInstance G F l) : (encIncoming E u).length = l + E.len := by
  simp [encIncoming, E.enc_len]

theorem encRunning_injective : Function.Injective (encRunning (l := l) E) := by
  rintro ⟨e, u, w, x⟩ ⟨e', u', w', x'⟩ h
  simp only [encRunning, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp)
  obtain ⟨h5, h6⟩ := List.append_inj h4 (by rw [E.enc_len, E.enc_len])
  have := List.ofFn_injective h3
  simp_all [E.enc_inj.eq_iff]

theorem encIncoming_injective : Function.Injective (encIncoming (l := l) E) := by
  rintro ⟨w, x⟩ ⟨w', x'⟩ h
  simp only [encIncoming] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have := List.ofFn_injective h1
  simp_all [E.enc_inj.eq_iff]

/-- The challenge input determines `U`, `u` and `cm_t`: no field of the statement can be changed
without changing `ρ`'s input. -/
theorem chalInput_injective {U U' : RunningInstance F G l} {u u' : IncomingInstance G F l}
    {c c' : G} (h : chalInput E U u c = chalInput E U' u' c') : U = U' ∧ u = u' ∧ c = c' := by
  unfold chalInput at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by
    simp [List.length_append, encRunning_length, encIncoming_length])
  obtain ⟨hU, hu⟩ := List.append_inj h1 (by rw [encRunning_length, encRunning_length])
  exact ⟨encRunning_injective E hU, encIncoming_injective E hu, E.enc_inj h2⟩

end Nova
end Sonobe
