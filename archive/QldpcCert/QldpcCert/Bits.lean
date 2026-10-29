import QldpcCert.Certificates

/-!
# Bitmask checkers, verified

`𝔽₂`-vectors are stored as natural numbers: bit `q` set means coordinate `q` is
`1`. The checkers use arithmetic and structurally recursive bitwise operations.
Their equivalence proofs connect them to Lean's standard bit operations.
Each comes with a theorem turning `= true` into the Mathlib statement the
certificates need. Instance files can then discharge every finite fact with
`decide +kernel`, and the compiler stays out of the trusted base.

The one idea beyond bookkeeping is the fast parity `fold`: XOR-ing the high half
of a number onto its low half preserves the parity of its bits. So `K` folds
reduce the parity of the low `2 ^ K` bits to bit `0`.
-/

open Finset Matrix

namespace Bits

/-- Bit `q` of `c`, as an element of `𝔽₂`. -/
def bit (c q : ℕ) : ZMod 2 := if c.testBit q then 1 else 0

/-- The vector on `n` qubits whose support is the set bits of `c` below `n`. -/
def vec (n c : ℕ) : Vec n := fun q => bit c q.val

/-- The matrix whose rows are the given bitmasks. -/
def ofRows (n : ℕ) (rows : List ℕ) : Matrix (Fin rows.length) (Fin n) (ZMod 2) :=
  fun i => vec n (rows.get i)

theorem bit_xor (a b q : ℕ) : bit (a ^^^ b) q = bit a q + bit b q := by
  unfold bit
  rw [Nat.testBit_xor]
  cases a.testBit q <;> cases b.testBit q <;> decide

theorem bit_land (a b q : ℕ) : bit (a &&& b) q = bit a q * bit b q := by
  unfold bit
  rw [Nat.testBit_and]
  cases a.testBit q <;> cases b.testBit q <;> decide

theorem bit_shiftRight (c s q : ℕ) : bit (c >>> s) q = bit c (s + q) := by
  unfold bit
  rw [Nat.testBit_shiftRight]

/-! ## Parity -/

/-- The sum in `𝔽₂` of the bits of `c` below `n`: their parity. -/
def parBelow (c n : ℕ) : ZMod 2 := ∑ q ∈ range n, bit c q

theorem parBelow_double (c s : ℕ) : parBelow c (2 * s) = parBelow (c ^^^ (c >>> s)) s := by
  unfold parBelow
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [bit_xor, bit_shiftRight]

/-- Force a natural-number accumulator before passing it to its continuation.
This prevents repeated kernel reduction of the same parity expression. -/
def strict {α : Sort u} (c : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn c (k 0) (fun p => k (p + 1))

theorem strict_eq {α : Sort u} (c : ℕ) (k : ℕ → α) : strict c k = k c := by
  cases c <;> rfl

/-- Bitwise operations with structural recursion and forced accumulators.
The budget bounds the number of divisions. Evaluation stops when either input is zero. -/

def bitwiseFuel : Nat → (Bool → Bool → Bool) → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k + 1, f, n, m =>
    strict n fun n => strict m fun m =>
    if n = 0 then
      if f false true then m else 0
    else if m = 0 then
      if f true false then n else 0
    else
      strict (bitwiseFuel k f (n / 2) (m / 2)) fun r =>
        if f (n % 2 = 1) (m % 2 = 1) then r + r + 1 else r + r

theorem bitwiseFuel_eq (k : Nat) (f : Bool → Bool → Bool) (n m : Nat)
    (hn : n < 2 ^ k) (hm : m < 2 ^ k) : bitwiseFuel k f n m = Nat.bitwise f n m := by
  induction k generalizing n m with
  | zero =>
    have : n = 0 := by simpa using hn
    have : m = 0 := by simpa using hm
    subst n; subst m
    simp [bitwiseFuel, Nat.bitwise]
  | succ k ih =>
    rw [bitwiseFuel, strict_eq, strict_eq, Nat.bitwise]
    split
    · rfl
    · split
      · rfl
      · have hn' : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
        have hm' : m / 2 < 2 ^ k := by rw [pow_succ] at hm; omega
        rw [strict_eq, ih _ _ hn' hm']

def fastBitwise (f : Bool → Bool → Bool) (n m : Nat) : Nat := bitwiseFuel (n + m + 1) f n m

theorem fastBitwise_eq (f : Bool → Bool → Bool) (n m : Nat) : fastBitwise f n m = Nat.bitwise f n m := by
  have hp : ∀ t : Nat, t < 2 ^ t := by
    intro t
    induction t with
    | zero => decide
    | succ t ih => rw [pow_succ]; omega
  apply bitwiseFuel_eq
  · have := hp (n + m + 1); omega
  · have := hp (n + m + 1); omega
/-- Kernel-friendly bitwise AND, equal to the standard operation. -/
def fastAnd (a b : Nat) : Nat := fastBitwise and a b

theorem fastAnd_eq (a b : Nat) : fastAnd a b = a &&& b := fastBitwise_eq and a b

/-- Kernel-friendly bitwise XOR, equal to the standard operation. -/
def fastXor (a b : Nat) : Nat := fastBitwise bne a b

theorem fastXor_eq (a b : Nat) : fastXor a b = a ^^^ b := fastBitwise_eq bne a b

/-- Fold `c` onto its low half `K` times. -/
def fold (c : ℕ) : ℕ → ℕ
  | 0 => c
  | K + 1 => strict c fun v => fold (fastXor v (v / 2 ^ (2 ^ K))) K

/-- After `K` folds, bit `0` is the parity of the low `2 ^ K` bits. -/
theorem bit_fold (c K : ℕ) : bit (fold c K) 0 = parBelow c (2 ^ K) := by
  induction K generalizing c with
  | zero => simp [fold, parBelow]
  | succ K ih =>
    rw [fold, strict_eq, fastXor_eq, ← Nat.shiftRight_eq_div_pow, ih,
      ← parBelow_double, pow_succ']

theorem parBelow_mod (c n m : ℕ) (h : n ≤ m) : parBelow (c % 2 ^ n) m = parBelow c n := by
  unfold parBelow
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.sum_range_add]
  have h1 : ∑ q ∈ range n, bit (c % 2 ^ n) q = ∑ q ∈ range n, bit c q :=
    Finset.sum_congr rfl fun q hq => by
      simp [bit, Nat.testBit_mod_two_pow, Finset.mem_range.mp hq]
  have h2 : ∑ q ∈ range d, bit (c % 2 ^ n) (n + q) = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [bit, Nat.testBit_mod_two_pow]
  rw [h1, h2, add_zero]

/-! ## Dot products and kernels -/

theorem vec_dotProduct (n a b : ℕ) : vec n a ⬝ᵥ vec n b = parBelow (a &&& b) n := by
  unfold parBelow
  rw [← Fin.sum_univ_eq_sum_range (fun q => bit (a &&& b) q) n]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [bit_land]
  rfl

/-- The bit `vec n a ⬝ᵥ vec n b`, computed with `K` folds (valid when `n ≤ 2 ^ K`). -/
def dotBit (n K a b : ℕ) : Bool := (fold (fastAnd a b % 2 ^ n) K).testBit 0

theorem vec_dotProduct_eq (n K a b : ℕ) (hK : n ≤ 2 ^ K) :
    vec n a ⬝ᵥ vec n b = if dotBit n K a b then 1 else 0 := by
  rw [vec_dotProduct, ← parBelow_mod _ n (2 ^ K) hK, ← bit_fold, dotBit, fastAnd_eq]
  rfl

theorem dotProduct_eq_one (n K a b : ℕ) (hK : n ≤ 2 ^ K) (h : dotBit n K a b = true) :
    vec n a ⬝ᵥ vec n b = 1 := by
  rw [vec_dotProduct_eq n K a b hK, h]
  rfl

theorem dotProduct_eq_zero (n K a b : ℕ) (hK : n ≤ 2 ^ K) (h : dotBit n K a b = false) :
    vec n a ⬝ᵥ vec n b = 0 := by
  rw [vec_dotProduct_eq n K a b hK, h]
  rfl

/-- `allOf p l` checks `p a` for every element of `l`. This plain structural
recursion is much cheaper for the kernel to evaluate than core's `List.all` on long
lists. -/
def allOf (p : ℕ → Bool) : List ℕ → Bool
  | [] => true
  | a :: as => p a && allOf p as

theorem allOf_spec (p : ℕ → Bool) (l : List ℕ) (h : allOf p l = true) :
    ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp
  | cons b bs ih =>
    simp only [allOf, Bool.and_eq_true] at h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact ih h.2 a ha

/-- Checks `H v = 0` for `H = ofRows n rows`. -/
def kerCheck (n K : ℕ) (rows : List ℕ) (v : ℕ) : Bool := allOf (fun a => !dotBit n K a v) rows

theorem mulVec_eq_zero (n K : ℕ) (hK : n ≤ 2 ^ K) (rows : List ℕ) (v : ℕ)
    (h : kerCheck n K rows v = true) : (ofRows n rows).mulVec (vec n v) = 0 := by
  funext i
  have hi := allOf_spec _ rows h (rows.get i) (List.get_mem rows i)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hi
  exact dotProduct_eq_zero n K _ v hK hi

/-- Checks `HX * HZᵀ = 0`. -/
def commCheck (n K : ℕ) (xs zs : List ℕ) : Bool :=
  allOf (fun a => allOf (fun b => !dotBit n K a b) zs) xs

theorem comm_of_check (n K : ℕ) (hK : n ≤ 2 ^ K) (xs zs : List ℕ)
    (h : commCheck n K xs zs = true) : ofRows n xs * (ofRows n zs).transpose = 0 := by
  ext i j
  have h1 := allOf_spec _ xs h (xs.get i) (List.get_mem xs i)
  have h2 := allOf_spec _ zs h1 (zs.get j) (List.get_mem zs j)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h2
  rw [Matrix.mul_apply', Matrix.zero_apply]
  exact dotProduct_eq_zero n K _ _ hK h2

/-! ## Indexed iteration -/

/-- `allIdx p l k` checks `p (k + i) (l[i])` for every index `i` of `l`. -/
def allIdx {α : Type*} (p : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | a :: as, k => p k a && allIdx p as (k + 1)

theorem allIdx_spec {α : Type*} (p : ℕ → α → Bool) (l : List α) (k : ℕ) (h : allIdx p l k = true)
    (i : Fin l.length) : p (k + i) (l.get i) = true := by
  induction l generalizing k with
  | nil => exact i.elim0
  | cons a as ih =>
    simp only [allIdx, Bool.and_eq_true] at h
    cases i using Fin.cases with
    | zero => simpa using h.1
    | succ i =>
      have := ih (k + 1) h.2 i
      simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using this

/-- Arithmetic bit test, avoiding repeated one-bit shifts. -/
def testBitFast (c q : Nat) : Bool := decide (c / 2 ^ q % 2 = 1)

theorem testBitFast_eq (c q : Nat) : testBitFast c q = c.testBit q :=
  Nat.testBit_eq_decide_div_mod_eq.symm

/-! ## Rank lower bounds -/

/-- XOR of the rows whose position (counted from `k`) is a set bit of `t`. -/
def combine (t : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | r :: rs, k => fastXor (if testBitFast t k then r else 0) (combine t rs (k + 1))

theorem bit_combine (t : ℕ) (rows : List ℕ) (k q : ℕ) :
    bit (combine t rows k) q = ∑ i : Fin rows.length, bit t (k + i) * bit (rows.get i) q := by
  induction rows generalizing k with
  | nil => simp [combine, bit]
  | cons r rs ih =>
    rw [combine, testBitFast_eq, fastXor_eq, bit_xor, ih]
    change _ = ∑ i : Fin (rs.length + 1), bit t (k + i) * bit ((r :: rs).get i) q
    rw [Fin.sum_univ_succ]
    congr 1
    · simp only [Fin.val_zero, Nat.add_zero, List.get_cons_zero]
      unfold bit
      split_ifs <;> simp_all
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

theorem ofRows_mul_apply (n : ℕ) (ts rows : List ℕ) (i : Fin ts.length) (j : Fin n) :
    (ofRows rows.length ts * ofRows n rows) i j = bit (combine (ts.get i) rows 0) j := by
  rw [bit_combine, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ofRows, vec]

/-- Checks the pivot identities `(T * H) i (p j) = [i = j]`. -/
def pivotCheck (n : ℕ) (rows ts ps : List ℕ) : Bool :=
  allIdx (fun i t => strict (combine t rows 0) fun c =>
    allIdx (fun j p => testBitFast c (p % n) == (i == j)) ps 0) ts 0

theorem pivot_of_check (n : ℕ) (hn : 0 < n) (rows ts ps : List ℕ)
    (hlen : ps.length = ts.length) (h : pivotCheck n rows ts ps = true) (i j : Fin ts.length) :
    (ofRows rows.length ts * ofRows n rows) i ⟨ps.getD j 0 % n, Nat.mod_lt _ hn⟩ =
      if i = j then 1 else 0 := by
  have hj : (j : ℕ) < ps.length := by rw [hlen]; exact j.isLt
  rw [ofRows_mul_apply]
  show bit (combine (ts.get i) rows 0) (ps.getD j 0 % n) = _
  have h1 := allIdx_spec _ ts 0 h i
  rw [strict_eq] at h1
  have h2 := allIdx_spec _ ps 0 h1 ⟨j, hj⟩
  simp only [Nat.zero_add, beq_iff_eq, testBitFast_eq] at h2
  have hget : ps.getD j 0 = ps.get ⟨j, hj⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hget]
  unfold bit
  rw [h2]
  by_cases hij : i = j
  · simp [hij]
  · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, this]

/-- Rank lower bound: the rows of `H` span at least `ts.length` dimensions. -/
theorem rank_le_of_check (n : ℕ) (hn : 0 < n) (rows ts ps : List ℕ)
    (hlen : ps.length = ts.length) (h : pivotCheck n rows ts ps = true) :
    ts.length ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (ofRows n rows))) :=
  CSSCode.le_finrank_span_rows (ofRows n rows) (ofRows rows.length ts)
    (fun j => ⟨ps.getD j 0 % n, Nat.mod_lt _ hn⟩) (pivot_of_check n hn rows ts ps hlen h)

/-! ## Disjoint families and weights -/

/-- Checks that the masks in `ls` are pairwise disjoint. -/
def disjointCheck (ls : List ℕ) : Bool :=
  allIdx (fun i a => allIdx (fun j b => i == j || fastAnd a b == 0) ls 0) ls 0

theorem cover_le_one (n : ℕ) (ls : List ℕ) (h : disjointCheck ls = true) (q : Fin n) :
    (univ.filter fun i : Fin ls.length => vec n (ls.get i) q ≠ 0).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, vec, bit, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, not_not] at hi hj
  by_contra hij
  have h2 := allIdx_spec _ ls 0 (allIdx_spec _ ls 0 h i) j
  simp only [Nat.zero_add, Bool.or_eq_true, beq_iff_eq, fastAnd_eq] at h2
  rcases h2 with h2 | h2
  · exact hij (Fin.ext h2)
  · have := congrArg (fun c => c.testBit q) h2
    simp only [Nat.testBit_and, Nat.zero_testBit, hi, hj, Bool.and_self,
      Bool.true_eq_false] at this

/-- Number of set bits of `c` below `n`. -/
def popBelow (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => popBelow c n + (if testBitFast c n then 1 else 0)

theorem sum_range_eq_popBelow (c n : ℕ) :
    ∑ q ∈ range n, (if c.testBit q then 1 else 0) = popBelow c n := by
  induction n with
  | zero => simp [popBelow]
  | succ n ih => rw [Finset.sum_range_succ, ih, popBelow, testBitFast_eq]

theorem hammingNorm_vec (n c : ℕ) : hammingNorm (vec n c) = popBelow c n := by
  rw [← sum_range_eq_popBelow, ← Fin.sum_univ_eq_sum_range (fun q => if c.testBit q then 1 else 0)]
  unfold hammingNorm
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [vec, bit]
  split_ifs <;> simp_all

end Bits
