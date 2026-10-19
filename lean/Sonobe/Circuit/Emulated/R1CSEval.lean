import Sonobe.Circuit.Emulated.Congruent
import Sonobe.Circuit.EmuArithConcrete
import Sonobe.Arith.R1CS

/-!
The relaxed R1CS check over the emulated field (`R1CSVar::evaluate_r1cs` followed by
`enforce_equivalent`, r1cs/circuits.rs:64, :124) for one row:

  `(1 · (A_i·z)) · (B_i·z)  +  (−u) · (C_i·z)  ≡  e_i  (mod p₂)`.

`M_i·z` is a sum of constant-coefficient × variable products (`VectorMulGadget`, emulated.rs:1082),
computed limb-wise with no constraints. The two products of non-constant values are
`mul_unaligned`; `enforce_equivalent` is `enforce_congruent`.
-/

namespace Sonobe
namespace Gadget

open Finset

section Rows

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime] {ι : Type*} [Fintype ι]

theorem conv_zero_of {α : Type*} [Semiring α] {a b : ℕ → α} {n m k : ℕ}
    (ha : ∀ i, n ≤ i → a i = 0) (hb : ∀ j, m ≤ j → b j = 0) (hk : n + m ≤ k + 1) :
    conv a b k = 0 := by
  unfold conv
  refine sum_eq_zero fun i hi => ?_
  have := mem_range.mp hi
  by_cases h : n ≤ i
  · rw [ha i h, zero_mul]
  · rw [hb (k - i) (by omega), mul_zero]

/-- Number of limbs of the constant `v` (`compute_bounds`). -/
def clen (v : ℕ) : ℕ := (bitsLen (v : ℤ) + 31) / 32

theorem lt_pow_clen (v : ℕ) : v < 2 ^ (32 * clen v) := by
  have h1 : v < 2 ^ (v.size) := Nat.lt_size_self v
  have h2 : v.size ≤ 32 * clen v := by
    unfold clen bitsLen; rw [Int.natAbs_natCast]; omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)

theorem clen_le (v : ℕ) (h : v < 2 ^ (32 * 8)) : clen v ≤ 8 := by
  have : v.size ≤ 256 := Nat.size_le.mpr (by simpa using h)
  unfold clen bitsLen; rw [Int.natAbs_natCast]; omega

theorem mlimb_zero {v j : ℕ} (hj : clen v ≤ j) : mlimb v j = 0 := by
  unfold mlimb
  have : v < 2 ^ (32 * j) :=
    lt_of_lt_of_le (lt_pow_clen v) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.div_eq_of_lt this]; simp

/-- Coefficient rows: `Σ_c v_c · z_c` as limbs, integers and bounds. -/
def rowL (v : ι → ℕ) (zc : ι → ℕ → ZMod p1) : ℕ → ZMod p1 :=
  fun k => ∑ c, conv (constL p1 (v c)) (tr 8 (zc c)) k

def rowZ (v : ι → ℕ) (zc : ι → ℕ → ZMod p1) : ℕ → ℤ :=
  fun k => ∑ c, conv (constZ (v c)) (limbZ 8 (zc c)) k

def rowB (p2 : ℕ) (v : ι → ℕ) : ℕ → Bnd := fun k =>
  ⟨∑ c, (mulB (constB (v c)) (tightB p2) k).lo, ∑ c, (mulB (constB (v c)) (tightB p2) k).hi⟩

/-- Number of limbs of `Σ_c v_c · z_c` (`VectorMulGadget::mul`), over the nonzero entries. -/
def rlen (v : ι → ℕ) : ℕ := univ.sup fun c => if v c = 0 then 0 else clen (v c) + 7

omit [Fact (Nat.Prime p1)] in
theorem valid_sum {bs : ι → ℕ → Bnd} {a : ι → ℕ → ZMod p1} {z : ι → ℕ → ℤ}
    (h : ∀ c, Valid (bs c) (a c) (z c)) :
    Valid (fun k => ⟨∑ c, (bs c k).lo, ∑ c, (bs c k).hi⟩) (fun k => ∑ c, a c k)
      (fun k => ∑ c, z c k) := fun k => by
  refine ⟨⟨sum_le_sum fun c _ => (h c k).1.1, sum_le_sum fun c _ => (h c k).1.2⟩, ?_⟩
  push_cast
  exact sum_congr rfl fun c _ => (h c k).2

theorem valid_row (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (v : ι → ℕ) {zc : ι → ℕ → ZMod p1}
    (hz : ∀ c, Canon p2 (zc c)) : Valid (rowB p2 v) (rowL v zc) (rowZ v zc) := by
  have := valid_sum (bs := fun c => mulB (constB (v c)) (tightB p2))
    (a := fun c => conv (constL p1 (v c)) (tr 8 (zc c)))
    (z := fun c => conv (constZ (v c)) (limbZ 8 (zc c)))
    fun c => valid_mul (const_valid (v c)) (tight_valid hbits (hz c))
  exact this

theorem rlen_ge {v : ι → ℕ} (c : ι) (h : v c ≠ 0) : clen (v c) + 7 ≤ rlen v := by
  unfold rlen
  have := Finset.le_sup (f := fun c => if v c = 0 then 0 else clen (v c) + 7) (mem_univ c)
  simpa [h] using this

theorem rlen_le {v : ι → ℕ} (h : ∀ c, v c < 2 ^ (32 * 8)) : rlen v ≤ 15 := by
  unfold rlen
  refine Finset.sup_le fun c _ => ?_
  have := clen_le _ (h c)
  split_ifs <;> omega

omit [Fact (Nat.Prime p1)] in
theorem rowZ_zero {v : ι → ℕ} {zc : ι → ℕ → ZMod p1} {k : ℕ} (hk : rlen v ≤ k) : rowZ v zc k = 0 := by
  unfold rowZ
  refine sum_eq_zero fun c _ => ?_
  by_cases h : v c = 0
  · have : constZ (v c) = fun _ => 0 := by funext i; simp [constZ, h, mlimb]
    simp [conv, this]
  · have := rlen_ge c h
    exact conv_zero_of (n := clen (v c)) (m := 8)
      (fun i hi => by simp [constZ, mlimb_zero hi])
      (fun j hj => by simp [limbZ, show ¬ j < 8 by omega]) (by omega)

omit [Fact (Nat.Prime p2)] in
theorem rowB_zero (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {v : ι → ℕ} {k : ℕ} (hk : rlen v ≤ k) : rowB p2 v k = Bnd.zero := by
  unfold rowB
  have : ∀ c, mulB (constB (v c)) (tightB p2) k = Bnd.zero := by
    intro c
    by_cases h : v c = 0
    · have hb : ∀ i, constB (v c) i = Bnd.zero := fun i => by simp [constB, h, mlimb, Bnd.zero]
      simp only [mulB, hb, Bnd.mul_zero_left]
      simp [Bnd.zero]
    · have := rlen_ge c h
      exact mulB_zero (n := clen (v c)) (m := 8)
        (fun i hi => by simp [constB, mlimb_zero hi, Bnd.zero])
        (fun j hj => tightB_high p2 hbits (by omega)) (by omega)
  simp [this, Bnd.zero]


theorem intVal_sum (f : ι → ℕ → ℤ) (N : ℕ) :
    intVal (fun k => ∑ c, f c k) N = ∑ c, intVal (f c) N := by
  unfold intVal
  simp only [sum_mul]
  exact sum_comm

theorem intVal_term (hv : v < 2 ^ (32 * 8)) (z : ℕ → ZMod p1) {N : ℕ} (hN : v ≠ 0 → clen v + 7 ≤ N) :
    intVal (conv (constZ v) (limbZ 8 z)) N = v * (limbsVal 8 z : ℤ) := by
  by_cases h0 : v = 0
  · subst h0
    have : constZ 0 = fun _ => 0 := by funext i; simp [constZ, mlimb]
    simp [conv, this, intVal]
  · have hc := clen_le v hv
    rw [intVal_conv (n := clen v) (m := 8) (fun i hi => by simp [constZ, mlimb_zero hi])
      (fun j hj => by simp [limbZ, show ¬ j < 8 by omega]) (by have := hN h0; omega),
      intVal_limbZ_eq 8 z]
    congr 1
    unfold intVal
    have e := sum_mlimb v (clen v)
    rw [Nat.mod_eq_of_lt (lt_pow_clen v)] at e
    have e' : ((∑ i ∈ range (clen v), mlimb v i * 2 ^ (32 * i) : ℕ) : ℤ) = v := by exact_mod_cast e
    push_cast at e'
    rw [← e']
    exact sum_congr rfl fun i hi => by rw [constZ, if_pos (by have := mem_range.mp hi; omega)]

theorem intVal_row {v : ι → ℕ} (hv : ∀ c, v c < 2 ^ (32 * 8)) (zc : ι → ℕ → ZMod p1) {N : ℕ}
    (hN : rlen v ≤ N) : intVal (rowZ v zc) N = ∑ c, (v c : ℤ) * (limbsVal 8 (zc c) : ℤ) := by
  unfold rowZ
  rw [intVal_sum]
  exact sum_congr rfl fun c _ => intVal_term (hv c) (zc c) fun h => by have := rlen_ge c h; omega

theorem valid_tr {bs : ℕ → Bnd} {a : ℕ → ZMod p1} {z : ℕ → ℤ} {n : ℕ} (h : Valid bs a z)
    (hz : ∀ k, n ≤ k → z k = 0) (hb : ∀ k, n ≤ k → bs k = Bnd.zero) : Valid bs (tr n a) z := by
  intro k
  by_cases hk : k < n
  · simpa [tr, hk] using h k
  · refine ⟨by rw [hb k (by omega), hz k (by omega)]; simp [Bnd.Mem, Bnd.zero], ?_⟩
    simp [tr, hk, hz k (by omega)]

/-- The product of two limb vectors: either all operands are constant and the product is formed
without constraints, or the product limbs are hints pinned by the polynomial identity. -/
def ProdRel (n m : ℕ) (a b P : ℕ → ZMod p1) : Prop :=
  (0 < n ∧ 0 < m ∧ MulRel n m a b P) ∨ ∀ k < n + m - 1, P k = conv (tr n a) (tr m b) k

theorem prod_eq (hlen : n + m - 1 < p1) {a b P : ℕ → ZMod p1} (h : ProdRel n m a b P) :
    tr (n + m - 1) P = conv (tr n a) (tr m b) := by
  have hk : ∀ k < n + m - 1, P k = conv (tr n a) (tr m b) k := by
    rcases h with ⟨hn, hm, h⟩ | h
    · exact mulRel_sound hn hm hlen h
    · exact h
  funext k
  by_cases hk' : k < n + m - 1
  · simp [tr, hk', hk k hk']
  · have h0 : conv (tr n a) (tr m b) k = 0 :=
      conv_zero_of (n := n) (m := m) (fun i hi => by simp only [tr]; rw [if_neg (by omega)])
        (fun j hj => by simp only [tr]; rw [if_neg (by omega)]) (by omega)
    rw [h0]; simp only [tr]; rw [if_neg hk']

theorem zero_valid : Valid (fun _ => Bnd.zero) (fun _ => (0 : ZMod p1)) (fun _ => 0) :=
  fun _ => ⟨by simp [Bnd.Mem, Bnd.zero], by simp⟩

def oneL (p1 : ℕ) : ℕ → ZMod p1 := fun i => if i = 0 then 1 else 0
def oneZ : ℕ → ℤ := fun i => if i = 0 then 1 else 0
def oneB : ℕ → Bnd := fun i => if i = 0 then ⟨1, 1⟩ else Bnd.zero

theorem one_valid : Valid oneB (oneL p1) oneZ := by
  intro i
  by_cases h : i = 0 <;> simp [oneB, oneL, oneZ, h, Bnd.Mem, Bnd.zero]

def negB (p2 : ℕ) : ℕ → Bnd := subB (fun _ => Bnd.zero) (tightB p2)

end Rows

section Row

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime] {ι : Type*} [Fintype ι]

def negL (u : ℕ → ZMod p1) : ℕ → ZMod p1 := fun i => 0 - tr 8 u i
def negZ (u : ℕ → ZMod p1) : ℕ → ℤ := fun i => 0 - limbZ 8 u i

/-- Static bounds of `1 · (A_i z) · (B_i z) + (−u) · (C_i z)`. -/
def rowSelfB (p2 : ℕ) (A B C : ι → ℕ) : ℕ → Bnd :=
  addB (mulB (mulB oneB (rowB p2 A)) (rowB p2 B)) (mulB (negB p2) (rowB p2 C))

/-- The constraints of one row of the relaxed R1CS check; `A B C` are the (canonical) coefficients
of the row and `zc` the limbs of the assignment `(u, x, w)`. -/
def RowRel (p2 : ℕ) (A B C : ι → ℕ) (zc : ι → ℕ → ZMod p1) (u e : ℕ → ZMod p1) : Prop :=
  ∃ P1 P2 : ℕ → ZMod p1,
    ProdRel (rlen A) (rlen B) (conv (oneL p1) (tr (rlen A) (rowL A zc))) (rowL B zc) P1 ∧
    ProdRel 8 (rlen C) (negL u) (rowL C zc) P2 ∧
    CongRel p2 (rowSelfB p2 A B C) (max (rlen A + rlen B - 1) (8 + rlen C - 1))
      (fun k => tr (rlen A + rlen B - 1) P1 k + tr (8 + rlen C - 1) P2 k) e

theorem valid_row_tr (hbits : bitsLen ((p2 : ℤ) - 1) = 254) (v : ι → ℕ) {zc : ι → ℕ → ZMod p1}
    (hz : ∀ c, Canon p2 (zc c)) :
    Valid (rowB p2 v) (tr (rlen v) (rowL v zc)) (rowZ v zc) :=
  valid_tr (valid_row hbits v hz) (fun _ hk => rowZ_zero hk) (fun _ hk => rowB_zero hbits hk)

theorem row_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {A B C : ι → ℕ} (hA : ∀ c, A c < 2 ^ (32 * 8))
    (hB : ∀ c, B c < 2 ^ (32 * 8)) (hC : ∀ c, C c < 2 ^ (32 * 8)) {zc : ι → ℕ → ZMod p1}
    (hz : ∀ c, Canon p2 (zc c)) {u e : ℕ → ZMod p1} (hu : Canon p2 u) (he : Canon p2 e)
    (h : RowRel p2 A B C zc u e) :
    ∃ Q : ℤ, (∑ c, (A c : ℤ) * (limbsVal 8 (zc c) : ℤ)) * (∑ c, (B c : ℤ) * (limbsVal 8 (zc c) : ℤ)) +
        (-(limbsVal 8 u : ℤ)) * (∑ c, (C c : ℤ) * (limbsVal 8 (zc c) : ℤ)) =
      Q * p2 + (limbsVal 8 e : ℤ) := by
  obtain ⟨P1, P2, h1, h2, hc⟩ := h
  have hnA := rlen_le hA
  have hnB := rlen_le hB
  have hnC := rlen_le hC
  have hlen1 : rlen A + rlen B - 1 < p1 := by omega
  have hlen2 : 8 + rlen C - 1 < p1 := by omega
  have hp2' : (1 : ℤ) < p2 := by have := (Fact.out : p2.Prime).two_le; omega
  have hVA := valid_row_tr hbits A hz
  have hVB := valid_row_tr hbits B hz
  have hVC := valid_row_tr hbits C hz
  -- `1 · (A z)`
  have hX0 := valid_mul (one_valid (p1 := p1)) hVA
  have hX1z : ∀ k, rlen A ≤ k → conv oneZ (rowZ A zc) k = 0 := fun k hk =>
    conv_zero_of (n := 1) (m := rlen A) (fun i hi => by simp [oneZ, show i ≠ 0 by omega])
      (fun j hj => rowZ_zero hj) (by omega)
  have hX1b : ∀ k, rlen A ≤ k → mulB oneB (rowB p2 A) k = Bnd.zero := fun k hk =>
    mulB_zero (n := 1) (m := rlen A) (fun i hi => by simp [oneB, show i ≠ 0 by omega])
      (fun j hj => rowB_zero hbits hj) (by omega)
  have hX := valid_tr hX0 hX1z hX1b
  -- the two products
  have hP1 : Valid (mulB (mulB oneB (rowB p2 A)) (rowB p2 B)) (tr (rlen A + rlen B - 1) P1)
      (conv (conv oneZ (rowZ A zc)) (rowZ B zc)) := by
    rw [prod_eq hlen1 h1]; exact valid_mul hX hVB
  have hVn : Valid (negB p2) (tr 8 (negL u)) (negZ u) :=
    valid_tr (valid_sub zero_valid (tight_valid hbits hu))
      (fun k hk => by simp [negZ, limbZ, show ¬ k < 8 by omega])
      (fun k hk => by
        simp only [negB, subB, tightB_high p2 hbits (by omega : 7 < k)]
        simp [Bnd.sub, Bnd.zero])
  have hP2 : Valid (mulB (negB p2) (rowB p2 C)) (tr (8 + rlen C - 1) P2)
      (conv (negZ u) (rowZ C zc)) := by
    rw [prod_eq hlen2 h2]; exact valid_mul hVn hVC
  have hS := valid_add hP1 hP2
  have hz1 : ∀ k, rlen A + rlen B - 1 ≤ k → conv (conv oneZ (rowZ A zc)) (rowZ B zc) k = 0 :=
    fun k hk => conv_zero_of (n := rlen A) (m := rlen B) hX1z (fun j hj => rowZ_zero hj) (by omega)
  have hz2 : ∀ k, 8 + rlen C - 1 ≤ k → conv (negZ u) (rowZ C zc) k = 0 := fun k hk =>
    conv_zero_of (n := 8) (m := rlen C) (fun i hi => by simp [negZ, limbZ, show ¬ i < 8 by omega])
      (fun j hj => rowZ_zero hj) (by omega)
  have hb1 : ∀ k, rlen A + rlen B - 1 ≤ k →
      mulB (mulB oneB (rowB p2 A)) (rowB p2 B) k = Bnd.zero := fun k hk =>
    mulB_zero (n := rlen A) (m := rlen B) hX1b (fun j hj => rowB_zero hbits hj) (by omega)
  have hb2 : ∀ k, 8 + rlen C - 1 ≤ k → mulB (negB p2) (rowB p2 C) k = Bnd.zero := fun k hk =>
    mulB_zero (n := 8) (m := rlen C)
      (fun i hi => by
        simp only [negB, subB, tightB_high p2 hbits (by omega : 7 < i)]
        simp [Bnd.sub, Bnd.zero]) (fun j hj => rowB_zero hbits hj) (by omega)
  have hzS : ∀ k, max (rlen A + rlen B - 1) (8 + rlen C - 1) ≤ k →
      conv (conv oneZ (rowZ A zc)) (rowZ B zc) k + conv (negZ u) (rowZ C zc) k = 0 := fun k hk => by
    rw [hz1 k (by omega), hz2 k (by omega), add_zero]
  have hbS : ∀ k, max (rlen A + rlen B - 1) (8 + rlen C - 1) ≤ k → rowSelfB p2 A B C k = Bnd.zero :=
    fun k hk => by
      simp only [rowSelfB, addB, hb1 k (by omega), hb2 k (by omega)]
      simp [Bnd.add, Bnd.zero]
  have hS' := valid_tr hS hzS hbS
  obtain ⟨Q, hQ⟩ := cong_sound hp hp2 hbits hbS hS' he hc
  refine ⟨Q, ?_⟩
  rw [intVal_add, intVal_conv (n := rlen A) (m := rlen B) hX1z (fun j hj => rowZ_zero hj)
      (by omega),
    intVal_conv (n := 8) (m := rlen C)
      (fun i hi => by simp [negZ, limbZ, show ¬ i < 8 by omega]) (fun j hj => rowZ_zero hj)
      (by omega),
    intVal_conv (n := 1) (m := rlen A) (N := rlen A) (fun i hi => by simp [oneZ, show i ≠ 0 by omega])
      (fun j hj => rowZ_zero hj) (by omega),
    intVal_row hA zc le_rfl, intVal_row hB zc le_rfl, intVal_row hC zc le_rfl] at hQ
  have hn : intVal (negZ u) 8 = -(limbsVal 8 u : ℤ) := by
    have := intVal_sub (fun _ => (0 : ℤ)) (limbZ 8 u) 8
    rw [intVal_limbZ_eq] at this
    simpa [intVal, negZ] using this
  have h1' : intVal oneZ 1 = 1 := by simp [intVal, oneZ]
  rw [hn, h1'] at hQ
  linarith

end Row

section Check

variable {p1 p2 : ℕ} [Fact p1.Prime] [Fact p2.Prime] {m l nw : ℕ}

/-- The limbs of the assignment `(u, x, w)`. -/
def zlimbs (u : ℕ → ZMod p1) (x : Fin l → ℕ → ZMod p1) (w : Fin nw → ℕ → ZMod p1) :
    Col l nw → ℕ → ZMod p1 :=
  Sum.elim (fun _ => u) (Sum.elim x w)

/-- **The emulated relaxed-R1CS check**: every row satisfies `RowRel`. -/
def EmuR1CSC (p2 : ℕ) (R : R1CS (ZMod p2) m l nw) (u : ℕ → ZMod p1) (x : Fin l → ℕ → ZMod p1)
    (w : Fin nw → ℕ → ZMod p1) (e : Fin m → ℕ → ZMod p1) : Prop :=
  ∀ i : Fin m, RowRel p2 (fun c => (R.A i c).val) (fun c => (R.B i c).val)
    (fun c => (R.C i c).val) (zlimbs u x w) u (e i)

theorem emuR1CS_sound (hp : 2 ^ 32 + 2 ^ 33 < p1) (hp2 : p2 < 2 ^ (32 * 8))
    (hbits : bitsLen ((p2 : ℤ) - 1) = 254) {R : R1CS (ZMod p2) m l nw} {u : ℕ → ZMod p1}
    {x : Fin l → ℕ → ZMod p1} {w : Fin nw → ℕ → ZMod p1} {e : Fin m → ℕ → ZMod p1}
    (hu : Canon p2 u) (hx : ∀ j, Canon p2 (x j)) (hw : ∀ j, Canon p2 (w j))
    (he : ∀ j, Canon p2 (e j)) (h : EmuR1CSC p2 R u x w e) :
    R.RelaxedSat (emuV p2 u) (fun j => emuV p2 (x j)) (fun j => emuV p2 (w j))
      (fun j => emuV p2 (e j)) := by
  have hz : ∀ c, Canon p2 (zlimbs u x w c) := by
    rintro (c | c | c)
    · exact hu
    · exact hx c
    · exact hw c
  have hval : ∀ c, (R1CS.zvec (emuV p2 u) (fun j => emuV p2 (x j)) (fun j => emuV p2 (w j)) c) =
      emuV p2 (zlimbs u x w c) := by
    rintro (c | c | c) <;> rfl
  have hlt : ∀ M : ZMod p2, M.val < 2 ^ (32 * 8) := fun M =>
    lt_trans (ZMod.val_lt M) hp2
  funext i
  obtain ⟨Q, hQ⟩ := row_sound hp hp2 hbits (fun c => hlt _) (fun c => hlt _) (fun c => hlt _) hz hu
    (he i) (h i)
  have hc := congrArg (fun t : ℤ => (t : ZMod p2)) hQ
  simp only [Int.cast_add, Int.cast_mul, Int.cast_sum, Int.cast_neg, Int.cast_natCast,
    ZMod.natCast_self, mul_zero, zero_add] at hc
  have e1 : ∀ M : ZMod p2, ((M.val : ℕ) : ZMod p2) = M := ZMod.natCast_zmod_val
  simp only [R1CS.eval, R1CS.zvec, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]
  simp only [emuV, e1] at hc ⊢
  simpa [Sum.elim, zlimbs, sub_eq_add_neg] using hc

end Check

end Gadget
end Sonobe
