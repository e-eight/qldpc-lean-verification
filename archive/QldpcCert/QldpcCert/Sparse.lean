import QldpcCert.Bits

/-! Sparse row certificates avoid large bitwise operations in dot products. -/
open Finset Matrix
namespace Bits

def sparseVec {n : Nat} (s : Finset (Fin n)) : Vec n := fun q => if q ∈ s then 1 else 0

def sparseCount {n : Nat} (s : Finset (Fin n)) (b : Nat) : Nat :=
  ∑ q ∈ s, if testBitFast b q then 1 else 0

def sparseDot {n : Nat} (s : Finset (Fin n)) (b : Nat) : Bool :=
  decide (sparseCount s b % 2 = 1)

theorem sparse_dotProduct {n : Nat} (s : Finset (Fin n)) (b : Nat) :
    sparseVec s ⬝ᵥ vec n b = if sparseDot s b then 1 else 0 := by
  have he : sparseVec s ⬝ᵥ vec n b = ∑ q ∈ s, if testBitFast b q then (1 : ZMod 2) else 0 := by
    simp only [sparseVec, dotProduct, ite_mul, one_mul, zero_mul]
    have hs : (∑ q ∈ s, if q ∈ s then vec n b q else 0) =
        ∑ q : Fin n, if q ∈ s then vec n b q else 0 :=
      Finset.sum_subset (Finset.subset_univ s) (fun q _ hq => by simp [hq])
    rw [← hs]
    exact Finset.sum_congr rfl fun q hq => by simp [hq, vec, bit, testBitFast_eq]
  have hc : (sparseCount s b : ZMod 2) =
      ∑ q ∈ s, if testBitFast b q then (1 : ZMod 2) else 0 := by simp [sparseCount]
  rw [he, ← hc]
  have hm : ((sparseCount s b % 2 : Nat) : ZMod 2) = (sparseCount s b : ZMod 2) := by
    simp
  rw [← hm]
  have hlt := Nat.mod_lt (sparseCount s b) (by decide : 0 < 2)
  rcases (show sparseCount s b % 2 = 0 ∨ sparseCount s b % 2 = 1 by omega) with h | h
  · simp [sparseDot, h]
  · simp [sparseDot, h]

def sparseRowCheck {n : Nat} (a : Nat) (s : Finset (Fin n)) : Bool :=
  (List.finRange n).all fun q => testBitFast a q == decide (q ∈ s)

theorem vec_eq_sparse {n : Nat} (a : Nat) (s : Finset (Fin n))
    (h : sparseRowCheck a s = true) : vec n a = sparseVec s := by
  funext q
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  simp only [beq_iff_eq, testBitFast_eq] at hq
  simp [vec, bit, sparseVec, hq]

def sparseRowsCheck (n : Nat) (rows : List Nat) (supports : List (Finset (Fin n))) : Bool :=
  allIdx (fun i a => sparseRowCheck a (supports.getD i ∅)) rows 0

theorem sparseRows_spec (n : Nat) (rows : List Nat) (supports : List (Finset (Fin n)))
    (h : sparseRowsCheck n rows supports = true) (i : Fin rows.length) :
    vec n (rows.get i) = sparseVec (supports.getD i ∅) := by
  apply vec_eq_sparse
  simpa using allIdx_spec _ rows 0 h i

def sparseKerCheck (n : Nat) (rows : List Nat) (supports : List (Finset (Fin n))) (v : Nat) : Bool :=
  decide (rows.length ≤ supports.length) && supports.all (fun s => !sparseDot s v)

theorem mulVec_eq_zero_sparse (n : Nat) (rows : List Nat) (supports : List (Finset (Fin n)))
    (hrows : sparseRowsCheck n rows supports = true) (v : Nat)
    (h : sparseKerCheck n rows supports v = true) : (ofRows n rows).mulVec (vec n v) = 0 := by
  funext i
  simp only [sparseKerCheck, Bool.and_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  have hsize : rows.length ≤ supports.length := of_decide_eq_true hsize
  have hiLen : (i : Nat) < supports.length := lt_of_lt_of_le i.isLt hsize
  have hget : supports.getD i ∅ = supports.get ⟨i, hiLen⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiLen]
  have hi := List.all_eq_true.mp hall (supports.get ⟨i, hiLen⟩) (List.get_mem _ _)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hi
  change vec n (rows.get i) ⬝ᵥ vec n v = 0
  rw [sparseRows_spec n rows supports hrows i, hget, sparse_dotProduct, hi]
  rfl

theorem comm_of_sparse (n : Nat) (xs : List Nat) (supports : List (Finset (Fin n))) (zs : List Nat)
    (hrows : sparseRowsCheck n xs supports = true)
    (h : allOf (sparseKerCheck n xs supports) zs = true) :
    ofRows n xs * (ofRows n zs).transpose = 0 := by
  ext i j
  have hj := mulVec_eq_zero_sparse n xs supports hrows (zs.get j)
    (allOf_spec _ zs h _ (List.get_mem zs j))
  exact congrFun hj i

end Bits
