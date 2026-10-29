import QldpcVerification.Input.MatrixSpec
import Mathlib.Tactic

/-!
Kernel-evaluated sparse matrix and pivot certificates. The algorithms specialize
the earlier pilot's sparse checks, without importing the archived package.
-/

namespace QldpcVerification.Input.Sparse

open Finset Matrix Module

def bit (b q : ℕ) : Bool := decide (b / 2 ^ q % 2 = 1)
def vec (n b : ℕ) : Vec n := fun q => if bit b q then 1 else 0
def indicator {n : ℕ} (s : Finset (Fin n)) : Vec n := fun q => if q ∈ s then 1 else 0
def matrix {n : ℕ} (rows : List (Finset (Fin n))) :
    Matrix (Fin rows.length) (Fin n) (ZMod 2) := fun i => indicator (rows.get i)

def count {n : ℕ} (s : Finset (Fin n)) (b : ℕ) : ℕ :=
  ∑ q ∈ s, if bit b q then 1 else 0
def parity {n : ℕ} (s : Finset (Fin n)) (b : ℕ) : Bool := decide (count s b % 2 = 1)

theorem indicator_dot {n : ℕ} (s : Finset (Fin n)) (b : ℕ) :
    indicator s ⬝ᵥ vec n b = if parity s b then 1 else 0 := by
  have he : indicator s ⬝ᵥ vec n b = ∑ q ∈ s, if bit b q then (1 : ZMod 2) else 0 := by
    simp only [indicator, dotProduct, ite_mul, one_mul, zero_mul]
    have hs : (∑ q ∈ s, if q ∈ s then vec n b q else 0) =
        ∑ q : Fin n, if q ∈ s then vec n b q else 0 :=
      Finset.sum_subset (Finset.subset_univ s) (fun q _ hq => by simp [hq])
    rw [← hs]
    exact Finset.sum_congr rfl fun q hq => by simp [hq, vec]
  have hc : (count s b : ZMod 2) =
      ∑ q ∈ s, if bit b q then (1 : ZMod 2) else 0 := by simp [count]
  rw [he, ← hc, ← ZMod.natCast_mod (count s b) 2]
  have hm : count s b % 2 = 0 ∨ count s b % 2 = 1 := by omega
  rcases hm with h | h <;> simp [parity, h]

def allIdx {α : Type} (p : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | a :: as, k => p k a && allIdx p as (k + 1)

theorem allIdx_spec {α : Type} (p : ℕ → α → Bool) (l : List α) (k : ℕ)
    (h : allIdx p l k = true) (i : Fin l.length) : p (k + i) (l.get i) = true := by
  induction l generalizing k with
  | nil => exact Fin.elim0 i
  | cons a as ih =>
    simp only [allIdx, Bool.and_eq_true] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h.1
    · simpa [Nat.add_assoc, Nat.add_comm 1] using ih (k + 1) h.2 j

def vectorCheck {n : ℕ} (b : ℕ) (s : Finset (Fin n)) : Bool :=
  (List.finRange n).all fun q => bit b q == decide (q ∈ s)

theorem vec_eq_indicator {n : ℕ} (b : ℕ) (s : Finset (Fin n))
    (h : vectorCheck b s = true) : vec n b = indicator s := by
  funext q
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  simp only [beq_iff_eq] at hq
  simp [vec, indicator, hq]

def kernelCheck {n : ℕ} (rows : List (Finset (Fin n))) (b : ℕ) : Bool :=
  rows.all fun s => !parity s b

theorem kernel_of_check {n : ℕ} (rows : List (Finset (Fin n))) (b : ℕ)
    (h : kernelCheck rows b = true) : (matrix rows).mulVec (vec n b) = 0 := by
  funext i
  have hi := List.all_eq_true.mp h (rows.get i) (List.get_mem rows i)
  change indicator (rows.get i) ⬝ᵥ vec n b = 0
  rw [indicator_dot]
  simpa using hi

theorem indicator_dot_indicator {n : ℕ} (s t : Finset (Fin n)) :
    indicator s ⬝ᵥ indicator t = ((s ∩ t).card : ZMod 2) := by
  simp only [indicator, dotProduct, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have he : (univ.filter fun q => q ∈ s).filter (fun q => q ∈ t) = s ∩ t := by
    ext q; simp
  rw [Finset.sum_boole, he]

def commCheck {n : ℕ} (xs zs : List (Finset (Fin n))) : Bool :=
  xs.all fun x => zs.all fun z => decide ((x ∩ z).card % 2 = 0)

theorem comm_of_check {n : ℕ} (xs zs : List (Finset (Fin n)))
    (h : commCheck xs zs = true) : matrix xs * (matrix zs).transpose = 0 := by
  ext i j
  have hi := List.all_eq_true.mp h (xs.get i) (List.get_mem xs i)
  have hj := List.all_eq_true.mp hi (zs.get j) (List.get_mem zs j)
  change indicator (xs.get i) ⬝ᵥ indicator (zs.get j) = 0
  rw [indicator_dot_indicator, ← ZMod.natCast_mod _ 2, of_decide_eq_true hj]
  rfl

theorem rank_of_pivots {n m r : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (T : Matrix (Fin r) (Fin m) (ZMod 2)) (p : Fin r → Fin n)
    (hp : ∀ i j, (T * H) i (p j) = if i = j then 1 else 0) :
    r ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) := by
  let S := Submodule.span (ZMod 2) (Set.range H)
  have hmem (i) : (T * H) i ∈ S := by
    have he : (T * H) i = ∑ k, T i k • H k := by
      ext j; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [he]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let v : Fin r → S := fun i => ⟨(T * H) i, hmem i⟩
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hh := congrArg (fun s : S => (s : Vec n) (p j)) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, v, hp, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
    exact hh
  simpa using hli.fintype_card_le_finrank

def columnCheck {n : ℕ} (rows : List (Finset (Fin n))) (ps : List (Fin n))
    (cols : List (Finset (Fin rows.length))) : Bool :=
  allIdx (fun j p => (List.finRange rows.length).all fun i =>
    decide (p ∈ rows.get i) == decide (i ∈ cols.getD j ∅)) ps 0

def pivotCheck {m : ℕ} (ts : List ℕ) (cols : List (Finset (Fin m))) : Bool :=
  allIdx (fun i t => allIdx (fun j s => parity s t == (i == j)) cols 0) ts 0

theorem rank_of_check {n : ℕ} (rows : List (Finset (Fin n))) (ts : List ℕ)
    (ps : List (Fin n)) (cols : List (Finset (Fin rows.length)))
    (hlen : ps.length = ts.length) (hclen : cols.length = ps.length)
    (hc : columnCheck rows ps cols = true) (hp : pivotCheck ts cols = true) :
    ts.length ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (matrix rows))) := by
  apply rank_of_pivots (matrix rows) (fun i => vec rows.length (ts.get i))
    (fun j => ps.get ⟨j, by simpa [hlen] using j.isLt⟩)
  intro i j
  let jp : Fin ps.length := ⟨j, by simpa [hlen] using j.isLt⟩
  let jc : Fin cols.length := ⟨j, by simpa [hclen, hlen] using j.isLt⟩
  have he : (fun r => matrix rows r (ps.get jp)) = indicator (cols.get jc) := by
    funext r
    have hr := List.all_eq_true.mp (allIdx_spec _ ps 0 hc jp) r (List.mem_finRange r)
    have hget : cols.getD jp ∅ = cols.get jc := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem jc.isLt, jp, jc]
    simp only [Nat.zero_add, beq_iff_eq] at hr
    rw [hget] at hr
    change (if ps.get jp ∈ rows.get r then (1 : ZMod 2) else 0) = _
    unfold indicator
    split_ifs <;> simp_all
  rw [Matrix.mul_apply']
  change vec rows.length (ts.get i) ⬝ᵥ (fun r => matrix rows r (ps.get jp)) = _
  rw [he, dotProduct_comm, indicator_dot]
  have hh := allIdx_spec _ cols 0 (allIdx_spec _ ts 0 hp i) jc
  simp only [Nat.zero_add, beq_iff_eq] at hh
  rw [hh]
  by_cases hij : i = j
  · simp [hij, jc]
  · have hn : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, hn, jc]

theorem weight_eq {n : ℕ} (b : ℕ) :
    hammingNorm (vec n b) = ∑ q : Fin n, if bit b q then 1 else 0 := by
  rw [hammingNorm, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro q _
  cases h : bit b q <;> simp [vec, h]

def pairingCheck {n : ℕ} (supports : List (Finset (Fin n))) (masks : List ℕ) : Bool :=
  allIdx (fun i b => allIdx (fun j s => parity s b == (i == j)) supports 0) masks 0

theorem pairing_of_check {n : ℕ} (supports : List (Finset (Fin n))) (masks : List ℕ)
    (h : pairingCheck supports masks = true) (i : Fin masks.length) (j : Fin supports.length) :
    vec n (masks.get i) ⬝ᵥ indicator (supports.get j) =
      if (i : ℕ) = j then 1 else 0 := by
  rw [dotProduct_comm, indicator_dot]
  have hh := allIdx_spec _ supports 0 (allIdx_spec _ masks 0 h i) j
  simp only [Nat.zero_add, beq_iff_eq] at hh
  rw [hh]
  by_cases h : (i : ℕ) = j <;> simp [h]

def familyCheck {n : ℕ} (rows opposites : List (Finset (Fin n)))
    (base : ℕ) (family : List (ℕ × ℕ)) : Bool :=
  family.all fun bw => kernelCheck rows bw.1 &&
    opposites.all (fun s => parity s bw.1 == parity s base)

theorem family_kernel {n : ℕ} (rows opposites : List (Finset (Fin n)))
    (base : ℕ) (family : List (ℕ × ℕ)) (h : familyCheck rows opposites base family = true)
    (i : Fin family.length) : (matrix rows).mulVec (vec n (family.get i).1) = 0 := by
  have hh := List.all_eq_true.mp h (family.get i) (List.get_mem family i)
  simp only [Bool.and_eq_true] at hh
  exact kernel_of_check rows _ hh.1

theorem family_pair {n : ℕ} (rows opposites : List (Finset (Fin n)))
    (base : ℕ) (family : List (ℕ × ℕ)) (h : familyCheck rows opposites base family = true)
    (i : Fin family.length) (j : Fin opposites.length) :
    indicator (opposites.get j) ⬝ᵥ vec n (family.get i).1 =
      indicator (opposites.get j) ⬝ᵥ vec n base := by
  have hh := List.all_eq_true.mp h (family.get i) (List.get_mem family i)
  simp only [Bool.and_eq_true] at hh
  have hp := List.all_eq_true.mp hh.2
    (opposites.get j) (List.get_mem opposites j)
  rw [indicator_dot, indicator_dot, (beq_iff_eq.mp hp)]

theorem sum_map_eq {α : Type} (l : List α) (f : α → ℕ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simpa [Fin.sum_univ_succ] using congrArg (f a + ·) ih

def capCheck (n : ℕ) (family : List (ℕ × ℕ)) (cap : ℕ) : Bool :=
  (List.finRange n).all fun q => decide
    ((family.map fun bw => if bit bw.1 q then bw.2 else 0).sum ≤ cap)

theorem cap_of_check {n : ℕ} (family : List (ℕ × ℕ)) (cap : ℕ)
    (h : capCheck n family cap = true) (q : Fin n) :
    (∑ i : Fin family.length,
      if vec n (family.get i).1 q ≠ 0 then (family.get i).2 else 0) ≤ cap := by
  have hh := of_decide_eq_true (List.all_eq_true.mp h q (List.mem_finRange q))
  rw [sum_map_eq] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  have he (b : Bool) (w : ℕ) :
      (if (if b then (1 : ZMod 2) else 0) ≠ 0 then w else 0) =
        if b then w else 0 := by cases b <;> simp
  exact he _ _

end QldpcVerification.Input.Sparse
