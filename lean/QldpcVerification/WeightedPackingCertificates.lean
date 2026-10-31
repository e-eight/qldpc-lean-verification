import QldpcVerification.Distance566Certificates

/-! Natural weights and a checked row-mask table for sparse packing certificates.
Weights never expand into repeated representatives. Row witnesses still refer to
the original matrix rows, not merely to their syndromes or logical coordinates. -/

namespace QldpcVerification.WeightedPackingCertificates

open Input Input.Sparse Distance566Certificates Quantum.Stabilizer.Homological

abbrev RawRep := (ℕ × List ℕ) × ℕ
abbrev Rep (m : ℕ) := (ℕ × List (Fin m)) × ℕ

def decode {m : ℕ} [NeZero m] (r : RawRep) : Rep m :=
  ((r.1.1, r.1.2.map (Fin.ofNat m)), r.2)

def rangeCheck (n m : ℕ) (reps : List RawRep) : Bool :=
  reps.all fun r => decide (r.1.1 < 2 ^ n) && r.1.2.all (fun j => decide (j < m))

theorem rangeCheck_append (n m : ℕ) (a b : List RawRep) :
    rangeCheck n m (a ++ b) = (rangeCheck n m a && rangeCheck n m b) := by
  simp only [rangeCheck, List.all_append]

theorem mask_bound_of_rangeCheck {n m : ℕ} {reps : List RawRep}
    (h : rangeCheck n m reps = true) {r : RawRep} (hr : r ∈ reps) : r.1.1 < 2 ^ n := by
  have hh := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hh
  exact of_decide_eq_true hh.1

theorem decode_row_no_wrap {n m : ℕ} [NeZero m] {reps : List RawRep}
    (h : rangeCheck n m reps = true) {r : RawRep} (hr : r ∈ reps)
    {j : ℕ} (hj : j ∈ r.1.2) : (Fin.ofNat m j).val = j := by
  have hh := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hh
  exact Nat.mod_eq_of_lt (of_decide_eq_true (List.all_eq_true.mp hh.2 j hj))

def family {m : ℕ} (reps : List (Rep m)) : List (ℕ × ℕ) :=
  reps.map fun r => (r.1.1, r.2)

def weightedClassCheck {n : ℕ} (rows : List (Finset (Fin n))) (base : ℕ)
    (reps : List (Rep rows.length)) : Bool :=
  classCheck rows base (reps.map Prod.fst)

theorem weightedClassCheck_map_sound {n : ℕ} (rows : List (Finset (Fin n))) (base : ℕ)
    (reps : List (Rep rows.length)) (h : weightedClassCheck rows base reps = true)
    (i : Fin (family reps).length) :
    vec n ((family reps).get i).1 - vec n base ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
  have hi : (i : ℕ) < (reps.map Prod.fst).length := by
    simpa only [family, List.length_map] using i.isLt
  simpa only [family, List.get_eq_getElem, List.getElem_map] using
    classCheck_sound rows base (reps.map Prod.fst) h ⟨i, hi⟩

def rowMasksCheck {n : ℕ} (rows : List (Finset (Fin n)))
    (masks : Fin rows.length → ℕ) : Bool :=
  (List.finRange rows.length).all fun i => masks i == supportMask (rows.get i)

theorem rowMasksCheck_sound {n : ℕ} (rows : List (Finset (Fin n)))
    (masks : Fin rows.length → ℕ) (h : rowMasksCheck rows masks = true)
    (i : Fin rows.length) : masks i = supportMask (rows.get i) :=
  beq_iff_eq.mp (List.all_eq_true.mp h i (List.mem_finRange i))

def packedClassCheck {m : ℕ} (masks : Fin m → ℕ) (base : ℕ)
    (reps : List (Rep m)) : Bool :=
  reps.all fun r => r.1.1 == (base ^^^ F2Mask.xorList (r.1.2.map masks))

theorem packedClassCheck_append {m : ℕ} (masks : Fin m → ℕ) (base : ℕ)
    (a b : List (Rep m)) : packedClassCheck masks base (a ++ b) =
      (packedClassCheck masks base a && packedClassCheck masks base b) := by
  simp only [packedClassCheck, List.all_append]

theorem packedClassCheck_map_sound {n : ℕ} (rows : List (Finset (Fin n)))
    (masks : Fin rows.length → ℕ) (hmasks : rowMasksCheck rows masks = true)
    (base : ℕ) (reps : List (Rep rows.length))
    (h : packedClassCheck masks base reps = true) (i : Fin (family reps).length) :
    vec n ((family reps).get i).1 - vec n base ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
  apply weightedClassCheck_map_sound rows base reps ?_ i
  change (reps.map Prod.fst).all (fun r => rowCheck rows base r.1 r.2) = true
  rw [List.all_map]
  apply List.all_eq_true.mpr
  intro r hr
  have hh := List.all_eq_true.mp h r hr
  have he : r.1.2.map masks = r.1.2.map (fun j => supportMask (rows.get j)) := by
    apply List.map_congr_left
    intro j _
    exact rowMasksCheck_sound rows masks hmasks j
  simpa only [rowCheck, he] using hh

def capChunkCheck {n : ℕ} (qs : List (Fin n)) (reps : List (ℕ × ℕ)) (cap : ℕ) : Bool :=
  qs.all fun q => decide ((reps.map fun r => if bit r.1 q then r.2 else 0).sum ≤ cap)

theorem capChunkCheck_append {n : ℕ} (a b : List (Fin n)) (reps : List (ℕ × ℕ))
    (cap : ℕ) : capChunkCheck (a ++ b) reps cap =
      (capChunkCheck a reps cap && capChunkCheck b reps cap) := by
  simp only [capChunkCheck, List.all_append]

end QldpcVerification.WeightedPackingCertificates
