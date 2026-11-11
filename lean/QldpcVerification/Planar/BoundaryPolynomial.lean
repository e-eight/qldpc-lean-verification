import QldpcVerification.Planar.BoundaryResidue
import QldpcVerification.Planar.CutCharge

/-! Polynomial realization of the 84 actual722 boundary coordinates.

Outer rows are ordered 0, 1, 19, 20; each inner row has indices 0 through 20.
For the reflected orientation the same encoding is evaluated by columnResidue.
The maps do not assume that a polynomial is a physical syndrome.
-/

namespace QldpcVerification.Planar.BoundaryPolynomial

open Polynomial ChargeAlgebra BoundaryResidue

noncomputable section

abbrev Bivar := BulkExactness.Bivariate

/-- Encode one row as an inner-variable polynomial. -/
def rowPoly : Row →ₗ[F] F[X] where
  toFun c := ∑ j : Fin 21, monomial j.val (c j)
  map_add' c d := by simp [map_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, Finset.smul_sum, Polynomial.smul_monomial,
      RingHom.id_apply]

@[simp] theorem rowPoly_coeff (c : Row) (j : Fin 21) :
    (rowPoly c).coeff j.val = c j := by
  classical
  change (∑ k : Fin 21, monomial k.val (c k)).coeff j.val = _
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [show k.val ≠ j.val from fun h => hkj (Fin.ext h)]
  · simp

theorem rowPoly_coeff_zero (c : Row) (j : ℕ) (hj : 21 ≤ j) :
    (rowPoly c).coeff j = 0 := by
  classical
  change (∑ k : Fin 21, monomial k.val (c k)).coeff j = 0
  simp only [finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg (by have := k.isLt; omega)]

/-- ((row0,row1),(row19,row20)) in ordinary bivariate polynomial coordinates. -/
def encode : Boundary →ₗ[F] Bivar where
  toFun b := monomial 0 (rowPoly b.1.1) + monomial 1 (rowPoly b.1.2) +
    monomial 19 (rowPoly b.2.1) + monomial 20 (rowPoly b.2.2)
  map_add' b c := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' a b := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
      Polynomial.smul_monomial, RingHom.id_apply]

/-- Read the four boundary rows; for arbitrary input this is a truncation. -/
def extract : Bivar →ₗ[F] Boundary where
  toFun p := ((fun j => (p.coeff 0).coeff j.val, fun j => (p.coeff 1).coeff j.val),
    (fun j => (p.coeff 19).coeff j.val, fun j => (p.coeff 20).coeff j.val))
  map_add' p q := by ext j <;> simp
  map_smul' a p := by ext j <;> simp

@[simp] theorem encode_apply (b : Boundary) :
    encode b = monomial 0 (rowPoly b.1.1) + monomial 1 (rowPoly b.1.2) +
      monomial 19 (rowPoly b.2.1) + monomial 20 (rowPoly b.2.2) := rfl

@[simp] theorem encode_coeff_zero (b : Boundary) : (encode b).coeff 0 = rowPoly b.1.1 := by
  simp only [encode_apply, coeff_add, coeff_monomial]
  norm_num

@[simp] theorem encode_coeff_one (b : Boundary) : (encode b).coeff 1 = rowPoly b.1.2 := by
  simp only [encode_apply, coeff_add, coeff_monomial]
  norm_num

@[simp] theorem encode_coeff_nineteen (b : Boundary) :
    (encode b).coeff 19 = rowPoly b.2.1 := by
  simp only [encode_apply, coeff_add, coeff_monomial]
  norm_num

@[simp] theorem encode_coeff_twenty (b : Boundary) :
    (encode b).coeff 20 = rowPoly b.2.2 := by
  simp only [encode_apply, coeff_add, coeff_monomial]
  norm_num

theorem encode_outer_zero (b : Boundary) (i : ℕ)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h19 : i ≠ 19) (h20 : i ≠ 20) :
    (encode b).coeff i = 0 := by
  simp only [encode_apply, coeff_add, coeff_monomial,
    if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h19),
    if_neg (Ne.symm h20), add_zero]

theorem encode_gap (b : Boundary) (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 18) :
    (encode b).coeff i = 0 :=
  encode_outer_zero b i (by omega) (by omega) (by omega) (by omega)

@[simp] theorem extract_encode (b : Boundary) : extract (encode b) = b := by
  ext j
  · change ((encode b).coeff 0).coeff j.val = b.1.1 j
    rw [encode_coeff_zero, rowPoly_coeff]
  · change ((encode b).coeff 1).coeff j.val = b.1.2 j
    rw [encode_coeff_one, rowPoly_coeff]
  · change ((encode b).coeff 19).coeff j.val = b.2.1 j
    rw [encode_coeff_nineteen, rowPoly_coeff]
  · change ((encode b).coeff 20).coeff j.val = b.2.2 j
    rw [encode_coeff_twenty, rowPoly_coeff]

theorem extract_surjective : Function.Surjective extract := by
  intro b
  exact ⟨encode b, extract_encode b⟩

theorem encode_injective : Function.Injective encode := by
  intro b c h
  have he := congrArg extract h
  simpa only [extract_encode] using he

private theorem rowPoly_extract_row (p : Bivar) (hp : BulkExactness.InSquare 20 p) (i : ℕ) :
    rowPoly (fun j : Fin 21 => (p.coeff i).coeff j.val) = p.coeff i := by
  apply Polynomial.ext
  intro j
  by_cases hj : j < 21
  · exact rowPoly_coeff _ ⟨j, hj⟩
  · rw [rowPoly_coeff_zero _ j (by omega)]
    exact (BulkExactness.inSquare_coeff_zero hp i j (Or.inr (by omega))).symm

/-- Four boundary rows exhaust a square-supported polynomial with zero interior rows. -/
theorem encode_extract (p : Bivar) (hp : BulkExactness.InSquare 20 p)
    (hgap : ∀ i, 2 ≤ i → i ≤ 18 → p.coeff i = 0) : encode (extract p) = p := by
  change monomial 0 (rowPoly (fun j => (p.coeff 0).coeff j.val)) +
    monomial 1 (rowPoly (fun j => (p.coeff 1).coeff j.val)) +
    monomial 19 (rowPoly (fun j => (p.coeff 19).coeff j.val)) +
    monomial 20 (rowPoly (fun j => (p.coeff 20).coeff j.val)) = p
  rw [rowPoly_extract_row p hp, rowPoly_extract_row p hp,
    rowPoly_extract_row p hp, rowPoly_extract_row p hp]
  apply Polynomial.ext
  intro i
  by_cases h0 : i = 0
  · subst i
    simp only [coeff_add, coeff_monomial]
    norm_num
  by_cases h1 : i = 1
  · subst i
    simp only [coeff_add, coeff_monomial]
    norm_num
  by_cases h19 : i = 19
  · subst i
    simp only [coeff_add, coeff_monomial]
    norm_num
  by_cases h20 : i = 20
  · subst i
    simp only [coeff_add, coeff_monomial]
    norm_num
  have hz : p.coeff i = 0 := by
    by_cases hi : i ≤ 18
    · exact hgap i (by omega) hi
    · exact coeff_eq_zero_of_natDegree_lt (by have := hp.1; omega)
  simp only [coeff_add, coeff_monomial,
    if_neg (Ne.symm h0), if_neg (Ne.symm h1), if_neg (Ne.symm h19),
    if_neg (Ne.symm h20), hz, add_zero]

theorem encode_inner_zero (b : Boundary) (i j : ℕ) (hj : 20 < j) :
    ((encode b).coeff i).coeff j = 0 := by
  have hz (c : Row) : (rowPoly c).coeff j = 0 := rowPoly_coeff_zero c j (by omega)
  by_cases h0 : i = 0
  · subst i
    rw [encode_coeff_zero]
    exact hz _
  by_cases h1 : i = 1
  · subst i
    rw [encode_coeff_one]
    exact hz _
  by_cases h19 : i = 19
  · subst i
    rw [encode_coeff_nineteen]
    exact hz _
  by_cases h20 : i = 20
  · subst i
    rw [encode_coeff_twenty]
    exact hz _
  rw [encode_outer_zero b i h0 h1 h19 h20, coeff_zero]

theorem encode_inSquare (b : Boundary) : BulkExactness.InSquare 20 (encode b) := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact encode_outer_zero b i (by omega) (by omega) (by omega) (by omega)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Polynomial.ext
    intro j
    rw [BulkExactness.swap_coeff]
    simpa using encode_inner_zero b j i hi

/-- The cut at row two retains precisely the low side. -/
theorem below_two_encode (b : Boundary) :
    CutCharge.below 2 (encode b) =
      monomial 0 (rowPoly b.1.1) + monomial 1 (rowPoly b.1.2) := by
  apply Polynomial.ext
  intro i
  rw [CutCharge.coeff_below]
  by_cases hi : i < 2
  · have he : i = 0 ∨ i = 1 := by omega
    rcases he with rfl | rfl <;>
      simp only [encode_coeff_zero, encode_coeff_one, coeff_add, coeff_monomial] <;>
      norm_num
  · simp only [if_neg hi, coeff_add, coeff_monomial,
      if_neg (show 0 ≠ i by omega), if_neg (show 1 ≠ i by omega), zero_add]

private theorem eval_rowPoly (z : A) (c : Row) :
    eval₂RingHom (algebraMap F A) z (rowPoly c) = rowEval z c := by
  change eval₂RingHom (algebraMap F A) z (∑ j : Fin 21, monomial j.val (c j)) = _
  rw [map_sum]
  simp only [coe_eval₂RingHom, eval₂_monomial, rowEval_apply, Algebra.smul_def]

theorem residue_monomial_rowPoly (i : ℕ) (c : Row) :
    CutCharge.residue (monomial i (rowPoly c)) = x ^ i * rowEval y c := by
  change (monomial i (rowPoly c)).eval₂
    (eval₂RingHom (algebraMap F A) y) x = _
  rw [eval₂_monomial, eval_rowPoly, mul_comm]

theorem columnResidue_monomial_rowPoly (i : ℕ) (c : Row) :
    CutCharge.columnResidue (monomial i (rowPoly c)) = y ^ i * rowEval x c := by
  have hm (j : Fin 21) :
      CutCharge.columnResidue (monomial i (monomial j.val (c j))) =
        y ^ i * (c j • x ^ j.val) := by
    change CutCharge.residue (BulkExactness.swap (monomial i (monomial j.val (c j)))) = _
    rw [BulkExactness.swap, Polynomial.Bivariate.swap_monomial_monomial]
    simp only [CutCharge.residue, coe_eval₂RingHom, eval₂_monomial, Algebra.smul_def]
    ring
  change CutCharge.columnResidue (monomial i (∑ j : Fin 21, monomial j.val (c j))) = _
  rw [map_sum, map_sum]
  simp_rw [hm]
  rw [← Finset.mul_sum]
  rfl

/-- Total residue of the polynomial equals the concrete boundary-coordinate map. -/
theorem residue_encode (b : Boundary) : CutCharge.residue (encode b) = totalX b := by
  rw [encode_apply]
  simp only [map_add, residue_monomial_rowPoly, totalX_apply, lowX_apply, highX_apply,
    rowEval_apply]
  ring

theorem residue_below_two_encode (b : Boundary) :
    CutCharge.residue (CutCharge.below 2 (encode b)) = lowX b.1 := by
  rw [below_two_encode, map_add, residue_monomial_rowPoly, residue_monomial_rowPoly]
  simp [lowX_apply]

/-- Reflected coordinate presentation: outer exponents evaluate at y. -/
theorem columnResidue_encode (b : Boundary) :
    CutCharge.columnResidue (encode b) = totalZ b := by
  rw [encode_apply]
  simp only [map_add, columnResidue_monomial_rowPoly, totalZ_apply, lowZ_apply, highZ_apply,
    rowEval_apply]
  ring

theorem columnResidue_below_two_encode (b : Boundary) :
    CutCharge.columnResidue (CutCharge.below 2 (encode b)) = lowZ b.1 := by
  rw [below_two_encode, map_add, columnResidue_monomial_rowPoly,
    columnResidue_monomial_rowPoly]
  simp [lowZ_apply]

/-- Direct adapter for a square-supported syndrome with vanishing tested rows. -/
theorem residue_extract (p : Bivar) (hp : BulkExactness.InSquare 20 p)
    (hgap : ∀ i, 2 ≤ i → i ≤ 18 → p.coeff i = 0) :
    totalX (extract p) = CutCharge.residue p := by
  rw [← residue_encode, encode_extract p hp hgap]

theorem low_residue_extract (p : Bivar) (hp : BulkExactness.InSquare 20 p)
    (hgap : ∀ i, 2 ≤ i → i ≤ 18 → p.coeff i = 0) :
    leftX (extract p) = CutCharge.residue (CutCharge.below 2 p) := by
  rw [leftX_apply, ← residue_below_two_encode, encode_extract p hp hgap]

theorem columnResidue_extract (p : Bivar) (hp : BulkExactness.InSquare 20 p)
    (hgap : ∀ i, 2 ≤ i → i ≤ 18 → p.coeff i = 0) :
    totalZ (extract p) = CutCharge.columnResidue p := by
  rw [← columnResidue_encode, encode_extract p hp hgap]

theorem low_columnResidue_extract (p : Bivar) (hp : BulkExactness.InSquare 20 p)
    (hgap : ∀ i, 2 ≤ i → i ≤ 18 → p.coeff i = 0) :
    leftZ (extract p) = CutCharge.columnResidue (CutCharge.below 2 p) := by
  rw [leftZ_apply, ← columnResidue_below_two_encode, encode_extract p hp hgap]

end
end QldpcVerification.Planar.BoundaryPolynomial
