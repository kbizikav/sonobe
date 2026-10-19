import Sonobe.Circuit.CycleFold

/-!
`P.scalar_mul_le(bits) + Q` — the shape used both by the CycleFold circuit and by the secondary
fold verifier (`cm' = proof · ρ + U.cm`).
-/

namespace Sonobe
namespace Gadget

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [Short W] [W.IsElliptic]

/-- `scalar_mul_le` followed by the complete addition: the output is a valid projective point
representing `Q + ρ · P`. -/
theorem mulAdd_spec (h2 : (2 : F) ≠ 0) (hnr : ∀ e : F, e ^ 3 + W.a₄ * e + W.a₆ ≠ 0)
    {r : ℕ} (hord : ∀ P : W.toAffine.Point, P ≠ 0 → addOrderOf P = r) {n : ℕ} (hn : 1 ≤ n)
    (hrn : 2 ^ n < r) {G : F × F} {bits : ℕ → F}
    (hb : ∀ i < n, IsBool (bits i)) {P Q : PP F} (hP : P.OnCurve W.a₄ W.a₆)
    (hQ : Q.OnCurve W.a₄ W.a₆) (hQn : ¬ Q.IsZero) {w : SMWit F} (h : SMRel W n G bits P w) :
    (rcb W.a₄ W.a₆ (smOut W n G bits w) Q).OnCurve W.a₄ W.a₆ ∧
      ¬ (rcb W.a₄ W.a₆ (smOut W n G bits w) Q).IsZero ∧
      (rcb W.a₄ W.a₆ (smOut W n G bits w) Q).pt W =
        Q.pt W + natVal n (fun j => decide (bits j = 1)) • P.pt W := by
  obtain ⟨hS_c, hS_n, hS_p⟩ := scalar_mul_sound W h2 hnr hord hn hrn hb hP h
  obtain ⟨hR_c, hR_n, hR_p⟩ := rcb_spec W h2 hnr hS_c hQ hS_n hQn
  exact ⟨hR_c, hR_n, by rw [hR_p, hS_p, add_comm]⟩

end Gadget
end Sonobe
