import Sonobe.Transcript.Sponge
import Sonobe.IVC.Model
import Sonobe.Circuit.Coords

/-!
Concrete hash and Fiat–Shamir challenge of the augmented circuit.

Both the in-circuit sponge (`GriffinSpongeVar`) and the native one are the duplex sponge of
`Transcript/Sponge`; consecutive `add` calls on an absorbing sponge are one `add` of the
concatenation. Encodings follow the `Absorbable` impls: emulated field elements as
`[V mod 2^253, V / 2^253]`, native points as affine `(x, y)` with the identity as `(0, 0)`.
-/

namespace Sonobe
namespace Gadget

open Finset WeierstrassCurve WeierstrassCurve.Affine Sonobe.IVC Sonobe.Nova
open scoped Classical

noncomputable local instance decEqZModH {p : ℕ} : DecidableEq (ZMod p) :=
  fun a b => Classical.propDecidable (a = b)

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime]

/-! ### Sponge: many `add`s are one -/

section Sponge

variable (sp : SpongeCfg (ZMod p1))

theorem add_nil (S : SpongeState (ZMod p1) sp.t) : sp.add S [] = S := by simp [SpongeCfg.add]

theorem add_mode (S : SpongeState (ZMod p1) sp.t) (xs : List (ZMod p1)) (hx : xs ≠ []) :
    ∃ i, (sp.add S xs).mode = .absorbing i := by
  simp [SpongeCfg.add, hx]

/-- Successive `add`s of a list of pieces equal one `add` of their concatenation. -/
theorem addMany_eq (S : SpongeState (ZMod p1) sp.t) {i : ℕ} (hS : S.mode = .absorbing i)
    (Ls : List (List (ZMod p1))) : Ls.foldl sp.add S = sp.add S Ls.flatten := by
  induction Ls generalizing S i with
  | nil => simp [add_nil]
  | cons L Ls ih =>
    by_cases hL : L = []
    · subst hL; simp [add_nil] at *; exact ih S hS
    · obtain ⟨j, hj⟩ := add_mode sp S L hL
      simp only [List.foldl_cons, List.flatten_cons]
      rw [ih (sp.add S L) hj]
      by_cases hr : Ls.flatten = []
      · simp [hr, add_nil]
      · exact sp.add_append S L Ls.flatten i hS hL

end Sponge

/-! ### Encodings and hashes -/

section Enc

variable (p1 p2 : ℕ) [Fact p1.Prime] [Fact p2.Prime]

/-- `Absorbable` for an emulated element: its two 253-bit chunks. -/
def encE (v : ZMod p2) : List (ZMod p1) :=
  [(((v.val % 2 ^ 253 : ℕ)) : ZMod p1), (((v.val / 2 ^ 253 : ℕ)) : ZMod p1)]

def pr {α : Type*} (o : α × α) : List α := [o.1, o.2]

def encPtE (c : ZMod p2 × ZMod p2) : List (ZMod p1) := encE p1 p2 c.1 ++ encE p1 p2 c.2

/-- `RunningInstanceVar::absorb_into` for the primary instance: `u, x, cm_e, cm_w`. -/
def encRU1 (U : RawRU (ZMod p1) (ZMod p2 × ZMod p2)) : List (ZMod p1) :=
  [U.u, U.x 0] ++ encPtE p1 p2 U.cmE ++ encPtE p1 p2 U.cmW

/-- `IncomingInstanceVar::absorb_into`: `x, cm_w`. -/
def encIU1 (u : RawIU (ZMod p1) (ZMod p2 × ZMod p2)) : List (ZMod p1) :=
  [u.x 0] ++ encPtE p1 p2 u.cmW

variable {p1 p2}
variable (W2 : WeierstrassCurve (ZMod p1)) [Short W2] [W2.IsElliptic]

/-- The secondary running instance: emulated `u`, `x₀..x₆`, native points as affine pairs. -/
noncomputable def encRU2 (V : RunningInstance (ZMod p2) W2.toAffine.Point 7) : List (ZMod p1) :=
  encE p1 p2 V.u ++ (List.ofFn fun j : Fin 7 => encE p1 p2 (V.x j)).flatten ++
    pr (coordsOf W2 V.cmE) ++ pr (coordsOf W2 V.cmW)

variable (sp : SpongeCfg (ZMod p1))

/-- `new_with_pp_hash(pp).separate_domain(dom)`. -/
def spInit (pp : ZMod p1) (dom : List (ZMod p1)) : SpongeState (ZMod p1) sp.t :=
  sp.add (sp.add sp.init [pp]) dom

/-- Absorb `L` and squeeze one field element. -/
def hashOut (S0 : SpongeState (ZMod p1) sp.t) (L : List (ZMod p1)) : ZMod p1 :=
  ((sp.get (sp.add S0 L) 1).1).headD 0

/-- `H(pp, i, z₀, zᵢ, U, cf_U)` (circuits.rs:138-145). -/
noncomputable def hsC {sN : ℕ} (dS : List (ZMod p1)) (pp i : ZMod p1) (z0 zi : Fin sN → ZMod p1)
    (U : RawRU (ZMod p1) (ZMod p2 × ZMod p2)) (V : RunningInstance (ZMod p2) W2.toAffine.Point 7) :
    ZMod p1 :=
  hashOut sp (spInit sp pp dS)
    ([i] ++ List.ofFn z0 ++ List.ofFn zi ++ encRU1 p1 p2 U ++ encRU2 W2 V)

/-- The primary Fiat–Shamir challenge: the low 128 bits of the first squeezed element. -/
def ch1nC (dT : List (ZMod p1)) (pp : ZMod p1) (U : RawRU (ZMod p1) (ZMod p2 × ZMod p2))
    (u : RawIU (ZMod p1) (ZMod p2 × ZMod p2)) (π : ZMod p2 × ZMod p2) : ℕ :=
  (hashOut sp (spInit sp pp dT) (encRU1 p1 p2 U ++ encIU1 p1 p2 u ++ encPtE p1 p2 π)).val % 2 ^ 128

end Enc

end Gadget
end Sonobe
