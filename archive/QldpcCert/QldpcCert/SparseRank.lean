import QldpcCert.Sparse
open Finset Matrix
namespace Bits

def sparseColsCheck (n : Nat) (hn : 0 < n) (rows : List Nat)
    (supports : List (Finset (Fin n))) (ps : List Nat)
    (cols : List (Finset (Fin rows.length))) : Bool :=
  allIdx (fun j p => (List.finRange rows.length).all fun i =>
    decide ((⟨p % n, Nat.mod_lt _ hn⟩ : Fin n) ∈ supports.getD i ∅) ==
      decide (i ∈ cols.getD j ∅)) ps 0

theorem column_eq_sparse (n : Nat) (hn : 0 < n) (rows : List Nat)
    (supports : List (Finset (Fin n))) (ps : List Nat)
    (cols : List (Finset (Fin rows.length)))
    (hrows : sparseRowsCheck n rows supports = true)
    (hcols : sparseColsCheck n hn rows supports ps cols = true) (j : Fin ps.length) :
    (fun i => ofRows n rows i ⟨ps.get j % n, Nat.mod_lt _ hn⟩) =
      sparseVec (cols.getD j ∅) := by
  funext i
  have hj := allIdx_spec _ ps 0 hcols j
  have hi := List.all_eq_true.mp hj i (List.mem_finRange i)
  simp only [Nat.zero_add, beq_iff_eq] at hi
  change vec n (rows.get i) ⟨ps.get j % n, Nat.mod_lt _ hn⟩ = _
  rw [sparseRows_spec n rows supports hrows i]
  unfold sparseVec
  split_ifs <;> simp_all

def sparsePivotCheck (m : Nat) (ts : List Nat) (cols : List (Finset (Fin m))) : Bool :=
  allIdx (fun i t => allIdx (fun j s => sparseDot s t == (i == j)) cols 0) ts 0

theorem rank_le_sparse (n : Nat) (hn : 0 < n) (rows : List Nat)
    (supports : List (Finset (Fin n))) (ts ps : List Nat)
    (cols : List (Finset (Fin rows.length)))
    (hrows : sparseRowsCheck n rows supports = true)
    (hlen : ps.length = ts.length) (hcolslen : cols.length = ps.length)
    (hcols : sparseColsCheck n hn rows supports ps cols = true)
    (hpiv : sparsePivotCheck rows.length ts cols = true) :
    ts.length ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (ofRows n rows))) := by
  apply CSSCode.le_finrank_span_rows (ofRows n rows) (ofRows rows.length ts)
    (fun j => ⟨ps.getD j 0 % n, Nat.mod_lt _ hn⟩)
  intro i j
  have hj : (j : Nat) < ps.length := by rw [hlen]; exact j.isLt
  have hjc : (j : Nat) < cols.length := by rw [hcolslen]; exact hj
  have hget : ps.getD j 0 = ps.get ⟨j, hj⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [Matrix.mul_apply', hget]
  change vec rows.length (ts.get i) ⬝ᵥ
    (fun r => ofRows n rows r ⟨ps.get ⟨j, hj⟩ % n, Nat.mod_lt _ hn⟩) = _
  rw [column_eq_sparse n hn rows supports ps cols hrows hcols ⟨j, hj⟩,
    dotProduct_comm, sparse_dotProduct]
  have h1 := allIdx_spec _ ts 0 hpiv i
  have h2 := allIdx_spec _ cols 0 h1 ⟨j, hjc⟩
  have hgetc : cols.getD j ∅ = cols.get ⟨j, hjc⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjc]
  rw [hgetc]
  simp only [Nat.zero_add, beq_iff_eq] at h2
  rw [h2]
  by_cases hij : i = j
  · simp [hij]
  · have : (i : Nat) ≠ j := fun h => hij (Fin.ext h)
    simp [hij, this]
end Bits
