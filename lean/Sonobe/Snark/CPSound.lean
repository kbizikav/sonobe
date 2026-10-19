import Sonobe.Snark.LegoGroth16
import Sonobe.Arith.R1CS
import Sonobe.Commitment.Pedersen

/-!
The LegoGroth16 verifier (`crates/snarks/src/cp/legogroth16/mod.rs:514-547`) as a predicate over
abstract bilinear groups, and its **knowledge soundness at one call** (`ExtractsAt`) — the single
cryptographic assumption on the CP-SNARK. It says nothing about the decider circuit: acceptance
yields a satisfying assignment of the *R1CS the keys were generated for*, whose committed
variables open the public commitments.
-/

namespace Sonobe
namespace LegoGroth16

variable {F G₁ G₂ G_T : Type*} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂]
  [Module F G₂] [AddCommGroup G_T] [Module F G_T]

/-- Verifying key (`VerifyingKey`, mod.rs): `l` public inputs, `nc` commitments. `betaNeg`, `gammaNeg`,
`deltaNeg` are `-β, -γ, -δ` (in `G₂`), `linkC j = k_j a` for the commitments and `D`. -/
structure VK (G₁ G₂ : Type*) (l nc : ℕ) where
  alpha : G₁
  betaNeg : G₂
  gammaNeg : G₂
  deltaNeg : G₂
  abc : Fin (l + 1) → G₁
  linkC : Fin (nc + 1) → G₂
  linkANeg : G₂

/-- Proof: `A, C, D, π_link ∈ G₁`, `B ∈ G₂`. -/
structure Proof (G₁ G₂ : Type*) where
  A : G₁
  B : G₂
  C : G₁
  D : G₁
  pi : G₁

variable {l nc : ℕ}

/-- `g_ic = abc₀ + Σ x_i abc_{i+1}`. -/
def VK.gic (vk : VK G₁ G₂ l nc) (x : Fin l → F) : G₁ := vk.abc 0 + ∑ i, x i • vk.abc i.succ

/-- `verify`: the Groth16 pairing product and the link check. -/
def Accepts (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (vk : VK G₁ G₂ l nc) (x : Fin l → F) (c : Fin nc → G₁)
    (π : Proof G₁ G₂) : Prop :=
  e π.A π.B + e (π.D + vk.gic x) vk.gammaNeg + e π.C vk.deltaNeg + e vk.alpha vk.betaNeg = 0 ∧
    ∑ j : Fin nc, e (c j) (vk.linkC j.castSucc) + e π.D (vk.linkC (Fin.last nc)) +
      e π.pi vk.linkANeg = 0

/-- **Knowledge soundness of LegoGroth16 at one call**, for an R1CS `R` (public inputs `x`) whose
committed witness variables are `blocks w = (e, w')` and whose two commitments use the Pedersen keys
`ckE`, `ckW` (the CP-SNARK's `link` with hidden `o`): if the verifier accepts `(x, c, π)`, the
extractor's output `(w, o)` is a satisfying witness whose committed blocks open `c`. This is the
*only* assumption on the CP-SNARK. -/
def ExtractsAt {m l' nw m1 nw1 : ℕ}
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (vk : VK G₁ G₂ l' 2) (R : R1CS F m l' nw)
    (blocks : (Fin nw → F) → (Fin m1 → F) × (Fin nw1 → F))
    (ckE : PedersenKey F G₁ m1) (ckW : PedersenKey F G₁ nw1) (x : Fin l' → F) (c : Fin 2 → G₁)
    (π : Proof G₁ G₂) (w : Fin nw → F) (o : Fin 2 → F) : Prop :=
  Accepts e vk x c π → R.Sat x w ∧ c 0 = ckE.commit (blocks w).1 (o 0) ∧
    c 1 = ckW.commit (blocks w).2 (o 1)

/-- An honest call meets `ExtractsAt`: its witness is valid whatever the verifier does. -/
theorem ExtractsAt.of_valid {m l' nw m1 nw1 : ℕ}
    {e : G₁ →ₗ[F] G₂ →ₗ[F] G_T} {vk : VK G₁ G₂ l' 2} {R : R1CS F m l' nw}
    {blocks : (Fin nw → F) → (Fin m1 → F) × (Fin nw1 → F)}
    {ckE : PedersenKey F G₁ m1} {ckW : PedersenKey F G₁ nw1} {x : Fin l' → F} {c : Fin 2 → G₁}
    {π : Proof G₁ G₂} {w : Fin nw → F} {o : Fin 2 → F}
    (h : R.Sat x w ∧ c 0 = ckE.commit (blocks w).1 (o 0) ∧ c 1 = ckW.commit (blocks w).2 (o 1)) :
    ExtractsAt e vk R blocks ckE ckW x c π w o := fun _ => h

end LegoGroth16
end Sonobe
