import QldpcVerification.Planar.Syndrome722
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Actual matrix entries as full-syndrome coefficients

The reflection swaps the two species and reverses both physical coordinates.
It is not asserted to be a symmetry of the original code. The two finite
matrix/coefficient identities below are proved on coordinate impulses and
extended by linearity; neither matrix matching nor cycle matching is assumed.

PROPOSITION: source draft pending capped compilation, audit, and review.
No Lean process was run by the source author.
-/

namespace QldpcVerification.Planar.SyndromeMatrix722

abbrev F2 := Commutation.F2

open Polynomial Commutation
open Syndrome722

noncomputable section

/-- Swap blocks and reflect both board coordinates. -/
def reflectQ : Q ≃ Q where
  toFun q := (!q.1, (q.2.1.rev, q.2.2.rev))
  invFun q := (!q.1, (q.2.1.rev, q.2.2.rev))
  left_inv q := by
    rcases q with ⟨b, i, j⟩
    cases b <;> simp
  right_inv q := by
    rcases q with ⟨b, i, j⟩
    cases b <;> simp

@[simp] theorem reflectQ_involutive (q : Q) : reflectQ (reflectQ q) = q := by
  rcases q with ⟨b, i, j⟩
  cases b <;> simp [reflectQ]

/-- Pull physical vectors along the involution; weight is unchanged. -/
def reflectPhysical : physicalV ≃ₗ[F2] physicalV where
  toFun w q := w (reflectQ q)
  invFun w q := w (reflectQ q)
  left_inv w := by
    funext q
    simp
  right_inv w := by
    funext q
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem reflectPhysical_apply (w : physicalV) (b : Bool) (i j : Fin 19) :
    reflectPhysical w (b, (i, j)) = w (!b, (i.rev, j.rev)) := rfl

@[simp] theorem reflectPhysical_involutive (w : physicalV) :
    reflectPhysical (reflectPhysical w) = w := by
  funext q
  change w (reflectQ (reflectQ q)) = w q
  rw [reflectQ_involutive]

theorem reflectPhysical_weight (w : physicalV) :
    hammingNorm (reflectPhysical w) = hammingNorm w := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact reflectQ.sum_comp (fun q => if w q ≠ 0 then 1 else 0)

/-- Reflect a matrix's physical columns; the row labels are unchanged. -/
def reflectMatrix {ι : Type*} (M : Matrix ι Q F2) : Matrix ι Q F2 :=
  fun a q => M a (reflectQ q)

theorem reflectMatrix_mulVec {ι : Type*} (M : Matrix ι Q F2) (w : physicalV) :
    (reflectMatrix M).mulVec (reflectPhysical w) = M.mulVec w := by
  funext a
  exact reflectQ.sum_comp (fun q => M a q * w q)

private def mono (i j : ℕ) : Bivariate := monomial i (monomial j 1)

private theorem mono_coeff (i j k l : ℕ) :
    ((mono i j).coeff k).coeff l = if i = k ∧ j = l then (1 : F2) else 0 := by
  simp only [mono, coeff_monomial]
  split_ifs <;> simp_all [coeff_monomial]

private theorem f_mul_mono (i j : ℕ) :
    BulkExactness.f * mono i j =
      mono (i + 2) j + mono (i + 1) j + mono i (j + 2) := by
  simp only [mono, BulkExactness.f, BulkExactness.quadratic, BulkExactness.Y,
    add_mul, X_pow_mul_monomial, X_mul_monomial, C_mul_monomial]

private theorem g_mul_mono (i j : ℕ) :
    BulkExactness.g * mono i j =
      mono (i + 2) (j + 1) + mono (i + 2) (j + 2) + mono i j := by
  simp only [mono, BulkExactness.g, BulkExactness.companion, BulkExactness.t,
    BulkExactness.Y, add_mul, mul_assoc, X_pow_mul_monomial, X_mul_monomial,
    C_mul_monomial, map_add, one_mul]

private theorem pack_single (q : Q) (b : Bool) (i : Fin 19) :
    BoundaryRecurrence.pack 19 19 (fun k l => (Pi.single q (1 : F2) : physicalV) (b, (k, l))) i =
      if b = q.1 ∧ i = q.2.1 then monomial q.2.2.val 1 else 0 := by
  classical
  rcases q with ⟨a, k, l⟩
  by_cases hb : b = a
  · subst b
    by_cases hi : i = k
    · subst i
      simp [BoundaryRecurrence.pack, Pi.single_apply, Prod.mk.injEq, apply_ite]
    · simp [BoundaryRecurrence.pack, Pi.single_apply, Prod.mk.injEq, hi,
        eq_comm, apply_ite]
  · simp [BoundaryRecurrence.pack, Pi.single_apply, Prod.mk.injEq, hb,
      eq_comm, apply_ite]

private theorem blockEncode_single (q : Q) (b : Bool) :
    blockEncode b (Pi.single q (1 : F2) : physicalV) =
      if b = q.1 then mono q.2.1.val q.2.2.val else 0 := by
  classical
  change (∑ i : Fin 19, monomial i.val
    (BoundaryRecurrence.pack 19 19 (fun k l => (Pi.single q (1 : F2) : physicalV) (b, (k, l))) i)) = _
  simp_rw [pack_single]
  by_cases hb : b = q.1
  · simp [hb, mono, apply_ite]
  · simp [hb]

private theorem syndrome_single (q : Q) :
    fullSyndrome (Pi.single q (1 : F2) : physicalV) =
      if q.1 then BulkExactness.f * mono q.2.1.val q.2.2.val
        else BulkExactness.g * mono q.2.1.val q.2.2.val := by
  rcases q with ⟨b, i, j⟩
  cases b <;> simp [fullSyndrome_apply, encode, blockEncode_single]

private theorem reflectPhysical_single (q : Q) :
    reflectPhysical (Pi.single q (1 : F2) : physicalV) = (Pi.single (reflectQ q) (1 : F2) : physicalV) := by
  classical
  funext r
  by_cases hr : r = reflectQ q
  · subst r
    change (Pi.single q (1 : F2) : physicalV) (reflectQ (reflectQ q)) =
      (Pi.single (reflectQ q) (1 : F2) : physicalV) (reflectQ q)
    rw [reflectQ_involutive q]
    simp
  · have hn : reflectQ r ≠ q := by
      intro h
      apply hr
      have he := congrArg reflectQ h
      simpa only [reflectQ_involutive] using he
    change (Pi.single q (1 : F2) : physicalV) (reflectQ r) = (Pi.single (reflectQ q) (1 : F2) : physicalV) r
    simp [Pi.single_apply, hr, hn, eq_comm]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
private theorem x_impulse_coeff (q : Q) (a : ZAnchor) :
    ((fullSyndrome (Pi.single q (1 : F2) : physicalV)).coeff (a.1.val + 2)).coeff a.2.val =
      HZ a q := by
  rw [syndrome_single]
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · simp only [Bool.false_eq_true, if_false, g_mul_mono, coeff_add, mono_coeff]
    simp only [HZ, Bool.false_eq_true, if_false, zBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, gShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · simp only [if_true, f_mul_mono, coeff_add, mono_coeff]
    simp only [HZ, if_true, zBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, fShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
private theorem z_impulse_coeff (q : Q) (a : XAnchor) :
    ((fullSyndrome (reflectPhysical (Pi.single q (1 : F2) : physicalV))).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX a q := by
  rw [reflectPhysical_single, syndrome_single]
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change ((BulkExactness.f * mono i.rev.val j.rev.val).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX a (false, (i, j))
    rw [f_mul_mono]
    simp only [coeff_add, mono_coeff, Fin.val_rev]
    simp only [HX, Bool.false_eq_true, if_false, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, fShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change ((BulkExactness.g * mono i.rev.val j.rev.val).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX a (true, (i, j))
    rw [g_mul_mono]
    simp only [coeff_add, mono_coeff, Fin.val_rev]
    simp only [HX, if_true, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, gShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

/-- Coefficient checks at exactly the actual Z anchor coordinates. -/
def xCoefficientChecks : physicalV →ₗ[F2] (ZAnchor → F2) where
  toFun w a := ((fullSyndrome w).coeff (a.1.val + 2)).coeff a.2.val
  map_add' w z := by
    funext a
    simp
  map_smul' r w := by
    funext a
    simp

/-- Actual X anchors after physical reflection: (20-a, 18-b). -/
def zCoefficientChecks : physicalV →ₗ[F2] (XAnchor → F2) where
  toFun w a := ((fullSyndrome (reflectPhysical w)).coeff a.1.rev.val).coeff
    (a.2.rev.val + 2)
  map_add' w z := by
    funext a
    simp
  map_smul' r w := by
    funext a
    simp

theorem xCoefficientChecks_eq : xCoefficientChecks = HZ.mulVecLin := by
  apply (Pi.basisFun F2 Q).ext
  intro q
  funext a
  simpa only [Pi.basisFun_apply, xCoefficientChecks, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using x_impulse_coeff q a

theorem zCoefficientChecks_eq : zCoefficientChecks = HX.mulVecLin := by
  apply (Pi.basisFun F2 Q).ext
  intro q
  funext a
  simpa only [Pi.basisFun_apply, zCoefficientChecks, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using z_impulse_coeff q a

theorem x_tested_coeff (w : physicalV) (a : ZAnchor) :
    HZ.mulVec w a = ((fullSyndrome w).coeff (a.1.val + 2)).coeff a.2.val := by
  have h := congrArg (fun L : physicalV →ₗ[F2] (ZAnchor → F2) => L w a)
    xCoefficientChecks_eq
  exact h.symm

theorem z_tested_coeff (w : physicalV) (a : XAnchor) :
    HX.mulVec w a = ((fullSyndrome (reflectPhysical w)).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) := by
  have h := congrArg (fun L : physicalV →ₗ[F2] (XAnchor → F2) => L w a)
    zCoefficientChecks_eq
  exact h.symm

/-- Actual Z-check cycles have identically zero full-syndrome polynomials in rows 2..18. -/
theorem x_cycle_coeff (w : physicalV) (hw : HZ.mulVec w = 0)
    (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 18) :
    (fullSyndrome w).coeff i = 0 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j < 21
  · let a : ZAnchor := (⟨i - 2, by omega⟩, ⟨j, hj⟩)
    have he := (x_tested_coeff w a).symm.trans (congrFun hw a)
    have hi2 : i - 2 + 2 = i := by omega
    simpa [a, hi2] using he
  · simpa using fullSyndrome_coeff_zero w i j (Or.inr (by omega))

/-- Actual X-check cycles give zero columns after block/board reflection and variable swap. -/
theorem z_cycle_coeff (w : physicalV) (hw : HX.mulVec w = 0)
    (j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ 18) :
    (BulkExactness.swap (fullSyndrome (reflectPhysical w))).coeff j = 0 := by
  apply Polynomial.ext
  intro i
  rw [BulkExactness.swap_coeff]
  by_cases hi : i < 21
  · let a : XAnchor := ((⟨i, hi⟩ : Fin 21).rev, (⟨j - 2, by omega⟩ : Fin 17).rev)
    have he := (z_tested_coeff w a).symm.trans (congrFun hw a)
    have hj2 : j - 2 + 2 = j := by omega
    simpa [a, hj2] using he
  · simpa using fullSyndrome_coeff_zero (reflectPhysical w) i j (Or.inl (by omega))

theorem x_cycle_iff (w : physicalV) :
    HZ.mulVec w = 0 ↔ ∀ i : ℕ, 2 ≤ i → i ≤ 18 → (fullSyndrome w).coeff i = 0 := by
  constructor
  · exact x_cycle_coeff w
  · intro h
    funext a
    rw [x_tested_coeff]
    have ha := a.1.isLt
    rw [h (a.1.val + 2) (by omega) (by omega)]
    simp

theorem z_cycle_iff (w : physicalV) :
    HX.mulVec w = 0 ↔ ∀ j : ℕ, 2 ≤ j → j ≤ 18 →
      (BulkExactness.swap (fullSyndrome (reflectPhysical w))).coeff j = 0 := by
  constructor
  · exact z_cycle_coeff w
  · intro h
    funext a
    rw [z_tested_coeff]
    have ha := a.2.rev.isLt
    have he := congrArg (fun p : BulkExactness.A => p.coeff a.1.rev.val)
      (h (a.2.rev.val + 2) (by omega) (by omega))
    simpa only [BulkExactness.swap_coeff, coeff_zero] using he

end

end QldpcVerification.Planar.SyndromeMatrix722
