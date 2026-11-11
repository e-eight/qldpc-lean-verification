import QldpcVerification.Planar.Syndrome722
import QldpcVerification.Planar.CutCharge
import QldpcVerification.Planar.SyndromeMatrix722

/-!
# Vanishing charge of the actual rectangular stabilizers

Sparse support gives an empty pair of endpoint strips for every generator,
including the truncated boundary generators. The row or column cut lemma
then annihilates its charge. This file uses the literal finite matrix rows;
no hypothesis about unspecified generators replaces the matrix statements.

Pending capped replay and guarded axiom audit.
-/

namespace QldpcVerification.Planar.StabilizerCharge722

open Commutation Polynomial

noncomputable section

/-- A shifted X monomial cannot contribute outside its three-row strip. -/
theorem xBlock_row_zero (a : XAnchor) (s : Fin 3 → Commutation.Lattice)
    (hs : Commutation.Small s)
    (i j : Fin 19) (hout : i.val + 2 < a.1.val ∨ a.1.val < i.val) :
    xBlock a s (i, j) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk := hs k
  have he : cell (i, j) ≠ xAnchor a + s k := by
    intro h
    have hx := congrArg Prod.fst h
    change (i.val : ℤ) = (a.1.val : ℤ) - 2 + (s k).1 at hx
    omega
  exact if_neg he

/-- Both species of the actual X row lie in the same three-row strip. -/
theorem HX_row_zero (a : XAnchor) (b : Bool) (i j : Fin 19)
    (hout : i.val + 2 < a.1.val ∨ a.1.val < i.val) :
    HX a (b, (i, j)) = 0 := by
  cases b
  · exact xBlock_row_zero a fShift fShift_small i j hout
  · exact xBlock_row_zero a gShift gShift_small i j hout

/-- A shifted Z monomial cannot contribute outside its three-column strip. -/
theorem zBlock_column_zero (a : ZAnchor) (s : Fin 3 → Commutation.Lattice)
    (hs : Commutation.Small s)
    (i j : Fin 19) (hout : j.val + 2 < a.2.val ∨ a.2.val < j.val) :
    zBlock a s (i, j) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk := hs k
  have he : cell (i, j) ≠ zAnchor a - s k := by
    intro h
    have hy := congrArg Prod.snd h
    change (j.val : ℤ) = (a.2.val : ℤ) - (s k).2 at hy
    omega
  exact if_neg he

/-- Both species of the actual Z row lie in the same three-column strip. -/
theorem HZ_column_zero (a : ZAnchor) (b : Bool) (i j : Fin 19)
    (hout : j.val + 2 < a.2.val ∨ a.2.val < j.val) :
    HZ a (b, (i, j)) = 0 := by
  cases b
  · exact zBlock_column_zero a gShift gShift_small i j hout
  · exact zBlock_column_zero a fShift fShift_small i j hout

/-- An empty physical row is the zero outer coefficient polynomial. -/
theorem blockEncode_row_zero (w : Syndrome722.physicalV) (b : Bool) (i : Fin 19)
    (h : ∀ j : Fin 19, w (b, (i, j)) = 0) :
    (Syndrome722.blockEncode b w).coeff i.val = 0 := by
  apply Polynomial.ext
  intro j
  rw [coeff_zero]
  by_cases hj : j < 19
  · exact (Syndrome722.blockEncode_coeff w b i ⟨j, hj⟩).trans (h ⟨j, hj⟩)
  · exact Syndrome722.squareEncode_coeff_zero (fun i j => w (b, (i, j)))
      i.val j (Or.inr (by omega))

/-- An empty physical column is the zero outer coefficient after swapping variables. -/
theorem blockEncode_column_zero (w : Syndrome722.physicalV) (b : Bool) (j : Fin 19)
    (h : ∀ i : Fin 19, w (b, (i, j)) = 0) :
    (BulkExactness.swap (Syndrome722.blockEncode b w)).coeff j.val = 0 := by
  apply Polynomial.ext
  intro i
  rw [coeff_zero, BulkExactness.swap_coeff]
  by_cases hi : i < 19
  · exact (Syndrome722.blockEncode_coeff w b ⟨i, hi⟩ j).trans (h ⟨i, hi⟩)
  · exact Syndrome722.squareEncode_coeff_zero (fun i j => w (b, (i, j)))
      i j.val (Or.inl (by omega))

/-- Away from the low boundary the first two physical rows are empty. -/
theorem HX_low_rows_zero (a : XAnchor) (ha : 4 ≤ a.1.val) (b : Bool)
    (i : Fin 19) (hi : i.val ≤ 1) :
    (Syndrome722.blockEncode b (HX a)).coeff i.val = 0 := by
  apply blockEncode_row_zero
  intro j
  exact HX_row_zero a b i j (Or.inl (by omega))

/-- Low-boundary generators, including truncated ones, have empty last two rows. -/
theorem HX_high_rows_zero (a : XAnchor) (ha : a.1.val < 4) (b : Bool)
    (i : Fin 19) (hi : 17 ≤ i.val) :
    (Syndrome722.blockEncode b (HX a)).coeff i.val = 0 := by
  apply blockEncode_row_zero
  intro j
  exact HX_row_zero a b i j (Or.inr (by omega))

/-- Reflection turns the Z support strip into the directional strip indexed by `20-d`. -/
theorem reflectedHZ_column_zero (a : ZAnchor) (b : Bool) (j : Fin 19)
    (hout : j.val + 2 < 20 - a.2.val ∨ 20 - a.2.val < j.val) :
    (BulkExactness.swap (Syndrome722.blockEncode b
      (SyndromeMatrix722.reflectPhysical (HZ a)))).coeff j.val = 0 := by
  apply blockEncode_column_zero
  intro i
  change HZ a (!b, (i.rev, j.rev)) = 0
  apply HZ_column_zero
  have ha := a.2.isLt
  have hj := j.isLt
  simp only [Fin.val_rev]
  omega

/-- The reflected Z rows away from the low edge have empty first two columns. -/
theorem reflectedHZ_low_columns_zero (a : ZAnchor) (ha : 4 ≤ 20 - a.2.val)
    (b : Bool) (j : Fin 19) (hj : j.val ≤ 1) :
    (BulkExactness.swap (Syndrome722.blockEncode b
      (SyndromeMatrix722.reflectPhysical (HZ a)))).coeff j.val = 0 := by
  exact reflectedHZ_column_zero a b j (Or.inl (by omega))

/-- The reflected Z rows near the low edge have empty last two columns. -/
theorem reflectedHZ_high_columns_zero (a : ZAnchor) (ha : 20 - a.2.val < 4)
    (b : Bool) (j : Fin 19) (hj : 17 ≤ j.val) :
    (BulkExactness.swap (Syndrome722.blockEncode b
      (SyndromeMatrix722.reflectPhysical (HZ a)))).coeff j.val = 0 := by
  exact reflectedHZ_column_zero a b j (Or.inr (by omega))

/-- Every actual X generator is a Z-check cycle, by the proved finite commutation. -/
theorem HX_cycle (a : XAnchor) : HZ.mulVec (HX a) = 0 := by
  funext c
  change (∑ q : Q, HZ c q * HX a q) = 0
  simpa only [mul_comm] using rows_orthogonal a c

/-- Every actual Z generator is an X-check cycle. -/
theorem HZ_cycle (a : ZAnchor) : HX.mulVec (HZ a) = 0 := by
  funext c
  exact rows_orthogonal c a

/-- Low-row charge vanishes on every literal HX row, including all boundary rows. -/
theorem HX_lowCharge (a : XAnchor) :
    CutCharge.lowCharge (Syndrome722.encode (HX a)).1
      (Syndrome722.encode (HX a)).2 = 0 := by
  have hc (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 18) :
      (BulkExactness.g * (Syndrome722.encode (HX a)).1 +
        BulkExactness.f * (Syndrome722.encode (HX a)).2).coeff i = 0 :=
    SyndromeMatrix722.x_cycle_coeff (HX a) (HX_cycle a) i hi hi'
  by_cases ha : 4 ≤ a.1.val
  · apply CutCharge.row_cut_gap _ _ (k := 2) (by omega) (by omega) hc
    · exact HX_low_rows_zero a ha false 0 (by decide)
    · exact HX_low_rows_zero a ha false 1 (by decide)
    · exact HX_low_rows_zero a ha true 0 (by decide)
    · exact HX_low_rows_zero a ha true 1 (by decide)
  · have ha' : a.1.val < 4 := by omega
    apply CutCharge.row_cut_gap _ _ (k := 19) (by omega) (by omega) hc
    · exact HX_high_rows_zero a ha' false 17 (by decide)
    · exact HX_high_rows_zero a ha' false 18 (by decide)
    · exact HX_high_rows_zero a ha' true 17 (by decide)
    · exact HX_high_rows_zero a ha' true 18 (by decide)

/-- Low-column charge vanishes on every reflected literal HZ row. -/
theorem HZ_lowColumnCharge (a : ZAnchor) :
    CutCharge.lowColumnCharge
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical (HZ a))).1
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical (HZ a))).2 = 0 := by
  have hc (j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 18) :
      (BulkExactness.swap
        (BulkExactness.g *
            (Syndrome722.encode (SyndromeMatrix722.reflectPhysical (HZ a))).1 +
          BulkExactness.f *
            (Syndrome722.encode (SyndromeMatrix722.reflectPhysical (HZ a))).2)).coeff j = 0 :=
    SyndromeMatrix722.z_cycle_coeff (HZ a) (HZ_cycle a) j hj hj'
  by_cases ha : 4 ≤ 20 - a.2.val
  · apply CutCharge.column_cut_gap _ _ (k := 2) (by omega) (by omega) hc
    · exact reflectedHZ_low_columns_zero a ha false 0 (by decide)
    · exact reflectedHZ_low_columns_zero a ha false 1 (by decide)
    · exact reflectedHZ_low_columns_zero a ha true 0 (by decide)
    · exact reflectedHZ_low_columns_zero a ha true 1 (by decide)
  · have ha' : 20 - a.2.val < 4 := by omega
    apply CutCharge.column_cut_gap _ _ (k := 19) (by omega) (by omega) hc
    · exact reflectedHZ_high_columns_zero a ha' false 17 (by decide)
    · exact reflectedHZ_high_columns_zero a ha' false 18 (by decide)
    · exact reflectedHZ_high_columns_zero a ha' true 17 (by decide)
    · exact reflectedHZ_high_columns_zero a ha' true 18 (by decide)

end

end QldpcVerification.Planar.StabilizerCharge722
