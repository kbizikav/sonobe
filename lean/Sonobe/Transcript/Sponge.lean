import Mathlib

/-!
Duplex sponge of the transcript, generic in the permutation, modelled on arkworks' `PoseidonSponge`
(`ark-crypto-primitives` 0.6.0, `sponge/poseidon/mod.rs`), which
`crates/primitives/src/transcripts/poseidon/sponge.rs` wraps: `add_field_elements` is `absorb`,
`get_field_elements` is `squeeze_native_field_elements`. The gadget `PoseidonSpongeVar`
(`sponge/poseidon/constraints.rs`) has the same control flow over variables.

The proofs use a *lazy* element-wise machine (`add`, `get`), which permutes when it is about to
touch position `rate`. arkworks' loops work on whole slices (`absorb_internal`, `squeeze_internal`);
`absorb_eq_add` and `squeeze_eq_get` show they compute the same, for any permutation, so the
proofs cover every block the transcript absorbs and squeezes.
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

/-- The next index of the mode. -/
def SpongeState.idx {F : Type*} {t : ℕ} (S : SpongeState F t) : ℕ :=
  match S.mode with
  | .absorbing i => i
  | .squeezing i => i

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

/-- `add_field_elements`, element by element. -/
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

/-- `get_field_elements`, element by element. -/
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

/-! ### arkworks' batch loops -/

/-- Add `xs` to the rate from position `i`, without permuting. -/
def addList (s : Fin cfg.t → F) (i : ℕ) : List F → Fin cfg.t → F
  | [] => s
  | x :: xs => addList (cfg.addAt s i x) (i + 1) xs

/-- `absorb_internal` (`sponge/poseidon/mod.rs:124`): fill the rate from `i`, permuting when it is
full and elements remain. `fuel` bounds the loop. -/
def absorbLoop : ℕ → (Fin cfg.t → F) → ℕ → List F → (Fin cfg.t → F) × ℕ
  | 0, s, i, _ => (s, i)
  | fuel + 1, s, i, xs =>
    if i + xs.length ≤ cfg.rate then (cfg.addList s i xs, i + xs.length)
    else absorbLoop fuel (cfg.perm (cfg.addList s i (xs.take (cfg.rate - i)))) 0
      (xs.drop (cfg.rate - i))

/-- `CryptographicSponge::absorb` (`sponge/poseidon/mod.rs:236`): nothing for no elements; permute
first if the rate is full; absorbing after squeezing starts at 0. -/
def absorb (S : SpongeState F cfg.t) (xs : List F) : SpongeState F cfg.t :=
  if xs.isEmpty then S else
  let r := match S.mode with
    | .absorbing i =>
      if i = cfg.rate then cfg.absorbLoop (xs.length + 1) (cfg.perm S.st) 0 xs
      else cfg.absorbLoop (xs.length + 1) S.st i xs
    | .squeezing _ => cfg.absorbLoop (xs.length + 1) S.st 0 xs
  ⟨r.1, .absorbing r.2⟩

/-- `state[capacity + i .. capacity + i + n]`. -/
def readList (s : Fin cfg.t → F) (i : ℕ) : ℕ → List F
  | 0 => []
  | n + 1 => cfg.readAt s i :: readList s (i + 1) n

/-- `squeeze_internal` (`sponge/poseidon/mod.rs:156`): read the rate from `i`, permuting when it
is used up and outputs remain. -/
def squeezeLoop : ℕ → (Fin cfg.t → F) → ℕ → ℕ → List F × ((Fin cfg.t → F) × ℕ)
  | 0, s, i, _ => ([], (s, i))
  | fuel + 1, s, i, n =>
    if i + n ≤ cfg.rate then (cfg.readList s i n, (s, i + n))
    else
      let r := squeezeLoop fuel (cfg.perm s) 0 (n - (cfg.rate - i))
      (cfg.readList s i (cfg.rate - i) ++ r.1, r.2)

/-- `squeeze_native_field_elements` (`sponge/poseidon/mod.rs:324`): permute first after absorbing
or when the rate is used up. -/
def squeeze (S : SpongeState F cfg.t) (n : ℕ) : List F × SpongeState F cfg.t :=
  let r := match S.mode with
    | .absorbing _ => cfg.squeezeLoop (n + 1) (cfg.perm S.st) 0 n
    | .squeezing i =>
      if i = cfg.rate then cfg.squeezeLoop (n + 1) (cfg.perm S.st) 0 n
      else cfg.squeezeLoop (n + 1) S.st i n
  (r.1, ⟨r.2.1, .squeezing r.2.2⟩)

section Loops

variable {cfg} (hr : 0 < cfg.rate)
include hr

omit hr in
theorem foldl_absorb1_le : ∀ (xs : List F) (s : Fin cfg.t → F) (i : ℕ),
    i + xs.length ≤ cfg.rate → xs.foldl cfg.absorb1 (s, i) = (cfg.addList s i xs, i + xs.length)
  | [], _, _, _ => by simp [addList]
  | x :: xs, s, i, h => by
    have hi : i < cfg.rate := by simp at h; omega
    simp only [List.foldl_cons, absorb1, refill, if_neg hi.ne]
    rw [foldl_absorb1_le xs _ (i + 1) (by simp at h; omega)]
    simp [addList]; omega

theorem foldl_absorb1_full (x : F) (xs : List F) (s : Fin cfg.t → F) :
    (x :: xs).foldl cfg.absorb1 (s, cfg.rate) = (x :: xs).foldl cfg.absorb1 (cfg.perm s, 0) := by
  simp only [List.foldl_cons, absorb1, refill, ↓reduceIte, if_neg hr.ne]

theorem absorbLoop_eq : ∀ (fuel : ℕ) (s : Fin cfg.t → F) (i : ℕ) (xs : List F),
    i < cfg.rate → xs.length < fuel → cfg.absorbLoop fuel s i xs = xs.foldl cfg.absorb1 (s, i)
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, s, i, xs, hi, hf => by
    unfold absorbLoop
    split_ifs with hle
    · exact (foldl_absorb1_le xs s i hle).symm
    · have hk : cfg.rate - i < xs.length := by omega
      rw [absorbLoop_eq fuel _ 0 _ hr (by simp; omega)]
      conv_rhs => rw [← List.take_append_drop (cfg.rate - i) xs, List.foldl_append]
      rw [foldl_absorb1_le _ s i (by simp; omega)]
      have hlen : (xs.take (cfg.rate - i)).length = cfg.rate - i := by simp; omega
      rw [hlen, show i + (cfg.rate - i) = cfg.rate by omega]
      obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil (l := xs.drop (cfg.rate - i))
        (by simp; omega)
      rw [hys, foldl_absorb1_full hr]

/-- **arkworks' `absorb` is `add`**, for any permutation. -/
theorem absorb_eq_add (S : SpongeState F cfg.t) (hS : S.idx ≤ cfg.rate) (xs : List F) :
    cfg.absorb S xs = cfg.add S xs := by
  unfold absorb add
  by_cases hx : xs.isEmpty
  · simp [hx]
  · simp only [hx]
    have hne : xs ≠ [] := by simpa using hx
    obtain ⟨st, mode⟩ := S
    cases mode with
    | absorbing i =>
      simp only [SpongeState.idx] at hS
      by_cases hi : i = cfg.rate
      · subst hi
        simp only [↓reduceIte]
        obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
        rw [absorbLoop_eq hr _ _ _ _ hr (by simp), foldl_absorb1_full hr]
      · simp only [if_neg hi]
        rw [absorbLoop_eq hr _ _ _ _ (by omega) (by simp)]
    | squeezing i =>
      simp only
      rw [absorbLoop_eq hr _ _ _ _ hr (by simp)]

omit hr in
theorem squeezeN_le : ∀ (n : ℕ) (s : Fin cfg.t → F) (i : ℕ), i + n ≤ cfg.rate →
    cfg.squeezeN n (s, i) = (cfg.readList s i n, (s, i + n))
  | 0, _, _, _ => by simp [squeezeN, readList]
  | n + 1, s, i, h => by
    have hi : i < cfg.rate := by omega
    simp only [squeezeN, squeeze1, refill, if_neg hi.ne]
    rw [squeezeN_le n s (i + 1) (by omega)]
    simp [readList]; omega

theorem squeezeN_full (n : ℕ) (s : Fin cfg.t → F) :
    cfg.squeezeN (n + 1) (s, cfg.rate) = cfg.squeezeN (n + 1) (cfg.perm s, 0) := by
  simp only [squeezeN, squeeze1, refill, ↓reduceIte, if_neg hr.ne]

omit hr in
theorem squeezeN_add : ∀ (a b : ℕ) (st : (Fin cfg.t → F) × ℕ),
    cfg.squeezeN (a + b) st =
      ((cfg.squeezeN a st).1 ++ (cfg.squeezeN b (cfg.squeezeN a st).2).1,
        (cfg.squeezeN b (cfg.squeezeN a st).2).2)
  | 0, b, st => by simp [squeezeN]
  | a + 1, b, st => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [squeezeN]
    rw [squeezeN_add a b]
    simp

theorem squeezeLoop_eq : ∀ (fuel : ℕ) (s : Fin cfg.t → F) (i n : ℕ),
    i < cfg.rate → n < fuel → cfg.squeezeLoop fuel s i n = cfg.squeezeN n (s, i)
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, s, i, n, hi, hf => by
    unfold squeezeLoop
    split_ifs with hle
    · exact (squeezeN_le n s i hle).symm
    · rw [squeezeLoop_eq fuel _ 0 _ hr (by omega)]
      obtain ⟨m, hm⟩ : ∃ m, n - (cfg.rate - i) = m + 1 := ⟨n - (cfg.rate - i) - 1, by omega⟩
      conv_rhs => rw [show n = (cfg.rate - i) + (n - (cfg.rate - i)) by omega, squeezeN_add]
      rw [squeezeN_le _ s i (by omega), show i + (cfg.rate - i) = cfg.rate by omega, hm,
        squeezeN_full hr]

/-- **arkworks' `squeeze_native_field_elements` is `get`**, for any permutation. -/
theorem squeeze_eq_get (S : SpongeState F cfg.t) (hS : S.idx ≤ cfg.rate) (n : ℕ) :
    cfg.squeeze S n = cfg.get S n := by
  unfold squeeze get
  obtain ⟨st, mode⟩ := S
  cases mode with
  | absorbing i =>
    simp only
    rw [squeezeLoop_eq hr _ _ _ _ hr (by omega)]
  | squeezing i =>
    simp only [SpongeState.idx] at hS
    simp only [refill]
    by_cases hi : i = cfg.rate
    · simp only [if_pos hi]
      rw [squeezeLoop_eq hr _ _ _ _ hr (by omega)]
    · simp only [if_neg hi]
      rw [squeezeLoop_eq hr _ _ _ _ (by omega) (by omega)]

theorem foldl_absorb1_idx : ∀ (xs : List F) (a : (Fin cfg.t → F) × ℕ),
    a.2 ≤ cfg.rate → (xs.foldl cfg.absorb1 a).2 ≤ cfg.rate
  | [], _, h => h
  | x :: xs, a, h => by
    refine foldl_absorb1_idx xs _ ?_
    simp only [absorb1, refill]
    split_ifs <;> simp <;> omega

theorem squeezeN_idx : ∀ (n : ℕ) (a : (Fin cfg.t → F) × ℕ),
    a.2 ≤ cfg.rate → (cfg.squeezeN n a).2.2 ≤ cfg.rate
  | 0, _, h => h
  | n + 1, a, h => by
    refine squeezeN_idx n _ ?_
    simp only [squeeze1, refill]
    split_ifs <;> simp <;> omega

/-- The index stays within the rate, so `absorb_eq_add` and `squeeze_eq_get` apply to every state
a transcript reaches from `init`. -/
theorem add_idx (S : SpongeState F cfg.t) (hS : S.idx ≤ cfg.rate) (xs : List F) :
    (cfg.add S xs).idx ≤ cfg.rate := by
  unfold add
  split_ifs
  · exact hS
  · obtain ⟨st, mode⟩ := S
    simp only [SpongeState.idx] at hS ⊢
    cases mode with
    | absorbing i => exact foldl_absorb1_idx hr xs _ hS
    | squeezing i => exact foldl_absorb1_idx hr xs _ (Nat.zero_le _)

theorem get_idx (S : SpongeState F cfg.t) (hS : S.idx ≤ cfg.rate) (n : ℕ) :
    (cfg.get S n).2.idx ≤ cfg.rate := by
  unfold get
  obtain ⟨st, mode⟩ := S
  simp only [SpongeState.idx] at hS ⊢
  cases mode with
  | absorbing i => exact squeezeN_idx hr n _ (by simp)
  | squeezing i =>
    refine squeezeN_idx hr n _ ?_
    simp only [refill]
    split_ifs
    · simp
    · simpa using hS

omit hr in
theorem init_idx : (cfg.init).idx = 0 := rfl

end Loops

end SpongeCfg
end Sonobe
