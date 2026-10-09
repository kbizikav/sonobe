import Sonobe.Transcript.Griffin

/-!
Duplex sponge, modelled on `crates/primitives/src/transcripts/griffin/sponge.rs`
(`add_field_elements` :200, `get_field_elements` :223, `absorb_internal` :30,
`squeeze_internal` :62). Generic in the permutation.

Rust's batch loops (`absorb_internal`, `squeeze_internal`) permute exactly when the next element
would not fit in the rate, and never at the end of a call; this is the same as the *lazy*
element-wise machine below, which permutes when it is about to touch position `rate`.
-/

namespace Sonobe

structure SpongeCfg (F : Type*) where
  t : ℕ
  cap : ℕ
  rate : ℕ
  perm : (Fin t → F) → (Fin t → F)

inductive Mode
  | absorbing (next : ℕ)
  | squeezing (next : ℕ)

structure SpongeState (F : Type*) (t : ℕ) where
  st : Fin t → F
  mode : Mode

namespace SpongeCfg

variable {F : Type*} [Field F] (cfg : SpongeCfg F)

/-- `state[capacity + k] += x`. -/
def addAt (s : Fin cfg.t → F) (k : ℕ) (x : F) : Fin cfg.t → F :=
  fun j => if j.val = cfg.cap + k then s j + x else s j

def readAt (s : Fin cfg.t → F) (k : ℕ) : F :=
  if h : cfg.cap + k < cfg.t then s ⟨cfg.cap + k, h⟩ else 0

/-- Permute first if the rate part is full. -/
def refill (s : Fin cfg.t → F) (i : ℕ) : (Fin cfg.t → F) × ℕ :=
  if i = cfg.rate then (cfg.perm s, 0) else (s, i)

def absorb1 (a : (Fin cfg.t → F) × ℕ) (x : F) : (Fin cfg.t → F) × ℕ :=
  let b := cfg.refill a.1 a.2
  (cfg.addAt b.1 b.2 x, b.2 + 1)

/-- `add_field_elements` (sponge.rs:200). -/
def add (S : SpongeState F cfg.t) (xs : List F) : SpongeState F cfg.t :=
  if xs.isEmpty then S else
  let start : (Fin cfg.t → F) × ℕ :=
    match S.mode with
    | .absorbing i => (S.st, i)
    | .squeezing _ => (S.st, 0)
  let r := xs.foldl cfg.absorb1 start
  ⟨r.1, .absorbing r.2⟩

def squeeze1 (a : (Fin cfg.t → F) × ℕ) : F × ((Fin cfg.t → F) × ℕ) :=
  let b := cfg.refill a.1 a.2
  (cfg.readAt b.1 b.2, (b.1, b.2 + 1))

/-- Squeeze `n` elements from `(state, next index)`. -/
def squeezeN : ℕ → (Fin cfg.t → F) × ℕ → List F × ((Fin cfg.t → F) × ℕ)
  | 0, a => ([], a)
  | n + 1, a =>
    let r := cfg.squeeze1 a
    let q := squeezeN n r.2
    (r.1 :: q.1, q.2)

/-- `get_field_elements` (sponge.rs:223). -/
def get (S : SpongeState F cfg.t) (n : ℕ) : List F × SpongeState F cfg.t :=
  let start : (Fin cfg.t → F) × ℕ :=
    match S.mode with
    | .absorbing _ => (cfg.perm S.st, 0)
    | .squeezing i => cfg.refill S.st i
  let r := cfg.squeezeN n start
  (r.1, ⟨r.2.1, .squeezing r.2.2⟩)

def init : SpongeState F cfg.t := ⟨0, .absorbing 0⟩

/-- Absorbing in pieces is absorbing the concatenation (when the pieces are non-empty and the
sponge is already absorbing). -/
theorem add_append (S : SpongeState F cfg.t) (xs ys : List F) (i : ℕ)
    (hS : S.mode = .absorbing i) (hx : xs ≠ []) :
    cfg.add (cfg.add S xs) ys = cfg.add S (xs ++ ys) := by
  by_cases hy : ys = []
  · subst hy; simp [add, hx]
  · have hxy : xs ++ ys ≠ [] := by simp [hx]
    simp [add, hx, hy, hxy, hS, List.foldl_append]

end SpongeCfg
end Sonobe

namespace Sonobe
namespace GriffinParams

variable {F : Type*} [Field F] (p : GriffinParams F)

/-- `GriffinSponge`: capacity 1, rate `t - 1` (griffin/mod.rs:110). -/
def cfg : SpongeCfg F := ⟨p.t, 1, p.t - 1, p.permute⟩

/-- **Hash-chain bind.** A circuit sponge whose every permutation call is only constrained by
the `GriffinGadget` constraints behaves exactly like the specification sponge: its outputs are
determined by the absorbed inputs. -/
theorem circuit_sponge_bind (π' : (Fin p.t → F) → (Fin p.t → F))
    (h : ∀ s, p.PermRel s (π' s)) : ({ p.cfg with perm := π' } : SpongeCfg F) = p.cfg := by
  have : π' = p.permute := funext fun s => (p.permRel_iff s _).mp (h s)
  simp [cfg, this]

end GriffinParams
end Sonobe
