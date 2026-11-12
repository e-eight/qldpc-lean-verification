import QldpcVerification.Planar.RectangleFamilySyndrome

/-! Exact matrix/recurrence correspondence for arbitrary rectangles. -/
namespace QldpcVerification.Planar.RectangleFamilyMatrix

open Polynomial RectangleFamily RectangleFamilySyndrome

variable {m n : ℕ}

noncomputable section

/-- Swap blocks and reflect both board coordinates. -/
def reflectQ : Q m n ≃ Q m n where
  toFun q := (!q.1, (q.2.1.rev, q.2.2.rev))
  invFun q := (!q.1, (q.2.1.rev, q.2.2.rev))
  left_inv q := by
    rcases q with ⟨b, i, j⟩
    cases b <;> simp
  right_inv q := by
    rcases q with ⟨b, i, j⟩
    cases b <;> simp

@[simp] theorem reflectQ_involutive (q : Q m n) : reflectQ (reflectQ q) = q := by
  rcases q with ⟨b, i, j⟩
  cases b <;> simp [reflectQ]

/-- Pull physical vectors along the involution; weight is unchanged. -/
def reflectPhysical : V m n ≃ₗ[F2] V m n where
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

@[simp] theorem reflectPhysical_apply (w : V m n) (b : Bool) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    reflectPhysical w (b, (i, j)) = w (!b, (i.rev, j.rev)) := rfl

@[simp] theorem reflectPhysical_involutive (w : V m n) :
    reflectPhysical (reflectPhysical w) = w := by
  funext q
  change w (reflectQ (reflectQ q)) = w q
  rw [reflectQ_involutive]

theorem reflectPhysical_weight (w : V m n) :
    hammingNorm (reflectPhysical w) = hammingNorm w := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact reflectQ.sum_comp (fun q => if w q ≠ 0 then 1 else 0)

/-- Reflect a matrix's physical columns; the row labels are unchanged. -/
def reflectMatrix {ι : Type*} (M : Matrix ι (Q m n) F2) : Matrix ι (Q m n) F2 :=
  fun a q => M a (reflectQ q)

theorem reflectMatrix_mulVec {ι : Type*} (M : Matrix ι (Q m n) F2) (w : V m n) :
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

private theorem pack_single (q : Q m n) (b : Bool) (i : Fin (m + 2)) :
    BoundaryRecurrence.pack (m + 2) (n + 2) (fun k l => (Pi.single q (1 : F2) : V m n) (b, (k, l))) i =
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

private theorem blockEncode_single (q : Q m n) (b : Bool) :
    blockEncode m n b (Pi.single q (1 : F2) : V m n) =
      if b = q.1 then mono q.2.1.val q.2.2.val else 0 := by
  classical
  change (∑ i : Fin (m + 2), monomial i.val
    (BoundaryRecurrence.pack (m + 2) (n + 2) (fun k l => (Pi.single q (1 : F2) : V m n) (b, (k, l))) i)) = _
  simp_rw [pack_single]
  by_cases hb : b = q.1
  · simp [hb, mono, apply_ite]
  · simp [hb]

private theorem syndrome_single (q : Q m n) :
    fullSyndrome m n (Pi.single q (1 : F2) : V m n) =
      if q.1 then BulkExactness.f * mono q.2.1.val q.2.2.val
        else BulkExactness.g * mono q.2.1.val q.2.2.val := by
  rcases q with ⟨b, i, j⟩
  cases b <;> simp [fullSyndrome_apply, encode, blockEncode_single]

private theorem reflectPhysical_single (q : Q m n) :
    reflectPhysical (Pi.single q (1 : F2) : V m n) = (Pi.single (reflectQ q) (1 : F2) : V m n) := by
  classical
  funext r
  by_cases hr : r = reflectQ q
  · subst r
    change (Pi.single q (1 : F2) : V m n) (reflectQ (reflectQ q)) =
      (Pi.single (reflectQ q) (1 : F2) : V m n) (reflectQ q)
    rw [reflectQ_involutive q]
    simp
  · have hn : reflectQ r ≠ q := by
      intro h
      apply hr
      have he := congrArg reflectQ h
      simpa only [reflectQ_involutive] using he
    change (Pi.single q (1 : F2) : V m n) (reflectQ r) = (Pi.single (reflectQ q) (1 : F2) : V m n) r
    simp [Pi.single_apply, hr, hn, eq_comm]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
private theorem x_impulse_coeff (q : Q m n) (a : ZAnchor m n) :
    ((fullSyndrome m n (Pi.single q (1 : F2) : V m n)).coeff (a.1.val + 2)).coeff a.2.val =
      HZ m n a q := by
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
private theorem z_impulse_coeff (q : Q m n) (a : XAnchor m n) :
    ((fullSyndrome m n (reflectPhysical (Pi.single q (1 : F2) : V m n))).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX m n a q := by
  rw [reflectPhysical_single, syndrome_single]
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change ((BulkExactness.f * mono i.rev.val j.rev.val).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX m n a (false, (i, j))
    rw [f_mul_mono]
    simp only [coeff_add, mono_coeff, Fin.val_rev]
    simp only [HX, Bool.false_eq_true, if_false, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, fShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change ((BulkExactness.g * mono i.rev.val j.rev.val).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) = HX m n a (true, (i, j))
    rw [g_mul_mono]
    simp only [coeff_add, mono_coeff, Fin.val_rev]
    simp only [HX, if_true, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, gShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

/-- Coefficient checks at exactly the actual Z anchor coordinates. -/
def xCoefficientChecks : V m n →ₗ[F2] (ZAnchor m n → F2) where
  toFun w a := ((fullSyndrome m n w).coeff (a.1.val + 2)).coeff a.2.val
  map_add' w z := by
    funext a
    simp
  map_smul' r w := by
    funext a
    simp

/-- Actual X anchors after physical reflection: (20-a, 18-b). -/
def zCoefficientChecks : V m n →ₗ[F2] (XAnchor m n → F2) where
  toFun w a := ((fullSyndrome m n (reflectPhysical w)).coeff a.1.rev.val).coeff
    (a.2.rev.val + 2)
  map_add' w z := by
    funext a
    simp
  map_smul' r w := by
    funext a
    simp

theorem xCoefficientChecks_eq : xCoefficientChecks (m := m) (n := n) = (HZ m n).mulVecLin := by
  apply (Pi.basisFun F2 (Q m n)).ext
  intro q
  funext a
  simpa only [Pi.basisFun_apply, xCoefficientChecks, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using x_impulse_coeff q a

theorem zCoefficientChecks_eq : zCoefficientChecks (m := m) (n := n) = (HX m n).mulVecLin := by
  apply (Pi.basisFun F2 (Q m n)).ext
  intro q
  funext a
  simpa only [Pi.basisFun_apply, zCoefficientChecks, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply] using z_impulse_coeff q a

theorem x_tested_coeff (w : V m n) (a : ZAnchor m n) :
    (HZ m n).mulVec w a = ((fullSyndrome m n w).coeff (a.1.val + 2)).coeff a.2.val := by
  have h := congrArg (fun L : V m n →ₗ[F2] (ZAnchor m n → F2) => L w a)
    xCoefficientChecks_eq
  exact h.symm

theorem z_tested_coeff (w : V m n) (a : XAnchor m n) :
    (HX m n).mulVec w a = ((fullSyndrome m n (reflectPhysical w)).coeff a.1.rev.val).coeff
      (a.2.rev.val + 2) := by
  have h := congrArg (fun L : V m n →ₗ[F2] (XAnchor m n → F2) => L w a)
    zCoefficientChecks_eq
  exact h.symm

/-- Actual Z-check cycles have identically zero full-syndrome polynomials in rows 2..18. -/
theorem x_cycle_coeff (w : V m n) (hw : (HZ m n).mulVec w = 0)
    (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ m + 1) :
    (fullSyndrome m n w).coeff i = 0 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j < n + 4
  · let a : ZAnchor m n := (⟨i - 2, by omega⟩, ⟨j, hj⟩)
    have he := (x_tested_coeff w a).symm.trans (congrFun hw a)
    have hi2 : i - 2 + 2 = i := by omega
    simpa [a, hi2] using he
  · simpa using fullSyndrome_coeff_zero w i j (Or.inr (by omega))

/-- Actual X-check cycles give zero columns after block/board reflection and variable swap. -/
theorem z_cycle_coeff (w : V m n) (hw : (HX m n).mulVec w = 0)
    (j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ n + 1) :
    (BulkExactness.swap (fullSyndrome m n (reflectPhysical w))).coeff j = 0 := by
  apply Polynomial.ext
  intro i
  rw [BulkExactness.swap_coeff]
  by_cases hi : i < m + 4
  · let a : XAnchor m n := ((⟨i, hi⟩ : Fin (m + 4)).rev, (⟨j - 2, by omega⟩ : Fin n).rev)
    have he := (z_tested_coeff w a).symm.trans (congrFun hw a)
    have hj2 : j - 2 + 2 = j := by omega
    simpa [a, hj2] using he
  · simpa using fullSyndrome_coeff_zero (reflectPhysical w) i j (Or.inl (by omega))

theorem x_cycle_iff (w : V m n) :
    (HZ m n).mulVec w = 0 ↔ ∀ i : ℕ, 2 ≤ i → i ≤ m + 1 → (fullSyndrome m n w).coeff i = 0 := by
  constructor
  · exact x_cycle_coeff w
  · intro h
    funext a
    rw [x_tested_coeff]
    have ha := a.1.isLt
    rw [h (a.1.val + 2) (by omega) (by omega)]
    simp

theorem z_cycle_iff (w : V m n) :
    (HX m n).mulVec w = 0 ↔ ∀ j : ℕ, 2 ≤ j → j ≤ n + 1 →
      (BulkExactness.swap (fullSyndrome m n (reflectPhysical w))).coeff j = 0 := by
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
end QldpcVerification.Planar.RectangleFamilyMatrix
