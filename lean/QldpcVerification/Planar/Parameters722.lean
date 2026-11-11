import QldpcVerification.Planar.Commutation
import QldpcVerification.Planar.BoundaryRecurrence
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Parameters of the explicit rectangular matrices

The impulse identities connect the directional polynomial recurrences to
the actual matrices of `Commutation`. All coordinates and the Z reflection
are explicit. The final quotient is the kernel of the Z parity map modulo
the X row space, as a binary vector space. No distance or external-input
correspondence is asserted. Pending capped compilation and axiom audit.
-/

namespace QldpcVerification.Planar.Parameters722

open Commutation Polynomial

private theorem pack_impulse {N m : ℕ} (a : Fin N × Fin m) (r : F2) (i : Fin N) :
    BoundaryRecurrence.pack N m (fun i j => if (i, j) = a then r else 0) i =
      if i = a.1 then monomial a.2.val r else 0 := by
  classical
  rcases a with ⟨a, b⟩
  by_cases hi : i = a
  · subst i
    simp [BoundaryRecurrence.pack, Prod.mk.injEq, apply_ite]
  · simp [BoundaryRecurrence.pack, Prod.mk.injEq, hi, apply_ite]

private theorem entry_pack_impulse {N m : ℕ} (a : Fin N × Fin m) (r : F2) (k : ℕ) :
    BoundaryRecurrence.entry
      (BoundaryRecurrence.pack N m (fun i j => if (i, j) = a then r else 0)) k =
      if k = a.1.val then monomial a.2.val r else 0 := by
  classical
  unfold BoundaryRecurrence.entry
  split
  · rename_i h
    simpa only [Fin.ext_iff] using pack_impulse a r ⟨k, h⟩
  · rename_i h
    have hk : k ≠ a.1.val := by have := a.1.isLt; omega
    simp [hk]

private noncomputable def pulse {N m : ℕ} (a : Fin N × Fin m) (k : ℕ) : BoundaryRecurrence.P :=
  if k = a.1.val then monomial a.2.val 1 else 0

private theorem pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l : ℕ) :
    (pulse a k).coeff l = if k = a.1.val ∧ a.2.val = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, coeff_monomial]

private theorem X_pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l : ℕ) :
    ((X : BoundaryRecurrence.P) * pulse a k).coeff l =
      if k = a.1.val ∧ a.2.val + 1 = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, X_mul_monomial, coeff_monomial]

private theorem Xpow_pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l d : ℕ) :
    ((X : BoundaryRecurrence.P) ^ d * pulse a k).coeff l =
      if k = a.1.val ∧ a.2.val + d = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, X_pow_mul_monomial, coeff_monomial]

private theorem x_impulse_entry (a : XAnchor) (k : ℕ) :
    BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1))) k = pulse a k := by
  have hc : BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1) =
      (fun i j => if (i, j) = a then (1 : F2) else 0) := by
    funext i j
    simp [BoundaryRecurrence.xAnchorCoordinates, Pi.single_apply, eq_comm]
  rw [hc]
  exact entry_pack_impulse a 1 k

private theorem z_impulse_entry (a : ZAnchor) (k : ℕ) :
    BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1))) k =
      pulse (a.2.rev, a.1.rev) k := by
  have hc : BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1) =
      (fun i j => if (i, j) = (a.2.rev, a.1.rev) then (1 : F2) else 0) := by
    funext i j
    have he : a = (j.rev, i.rev) ↔ (i, j) = (a.2.rev, a.1.rev) := by
      simp only [Prod.ext_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using (congrArg Fin.rev h₂).symm,
          by simpa using (congrArg Fin.rev h₁).symm⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using (congrArg Fin.rev h₂).symm,
          by simpa using (congrArg Fin.rev h₁).symm⟩
    change (Pi.single a (1 : F2) : ZAnchor → F2) (j.rev, i.rev) = _
    have he' : (j.rev, i.rev) = a ↔ (i, j) = (a.2.rev, a.1.rev) := eq_comm.trans he
    simp only [Pi.single_apply, he']
  rw [hc]
  exact entry_pack_impulse (a.2.rev, a.1.rev) 1 k

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- The X synthesis of one anchor is exactly that row of the explicit matrix. -/
theorem xSynthesis_single (a : XAnchor) : BoundaryRecurrence.xSynthesis (Pi.single a 1) = HX a := by
  funext q
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1))) i.val +
        BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1))) (i.val + 1) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1)))
            (i.val + 2)).coeff j.val = _
    simp only [x_impulse_entry, coeff_add, pulse_coeff, Xpow_pulse_coeff]
    simp only [HX, Bool.false_eq_true, if_false, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, fShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change (((X : BoundaryRecurrence.P) + X ^ 2) *
        BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1))) i.val +
        BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.xAnchorCoordinates (Pi.single a 1)))
          (i.val + 2)).coeff j.val = _
    simp only [x_impulse_entry, add_mul, coeff_add, pulse_coeff,
      X_pulse_coeff, Xpow_pulse_coeff]
    simp only [HX, if_true, xBlock, Fin.sum_univ_succ, Fin.sum_univ_zero,
      gShift, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- Reflection and block exchange recover exactly the original Z matrix row. -/
theorem zSynthesis_single (a : ZAnchor) : BoundaryRecurrence.zSynthesis (Pi.single a 1) = HZ a := by
  funext q
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1)))
          (j.rev.val + 2) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1)))
            (j.rev.val + 1) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1)))
            j.rev.val).coeff i.rev.val = _
    simp only [z_impulse_entry, coeff_add, pulse_coeff, Xpow_pulse_coeff,
      Fin.val_rev, Prod.fst, Prod.snd]
    simp only [HZ, Bool.false_eq_true, if_false, zBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, gShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1))) j.rev.val +
        ((X : BoundaryRecurrence.P) + X ^ 2) *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack 21 17 (BoundaryRecurrence.zAnchorCoordinates (Pi.single a 1)))
            (j.rev.val + 2)).coeff i.rev.val = _
    simp only [z_impulse_entry, add_mul, coeff_add, pulse_coeff,
      X_pulse_coeff, Xpow_pulse_coeff, Fin.val_rev, Prod.fst, Prod.snd]
    simp only [HZ, if_true, zBlock, Fin.sum_univ_succ, Fin.sum_univ_zero,
      fShift, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

/-- Equality of linear maps, not just equality of their ranks. -/
theorem xSynthesis_eq : BoundaryRecurrence.xSynthesis = HX.transpose.mulVecLin := by
  apply (Pi.basisFun F2 XAnchor).ext
  intro a
  simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.transpose_apply] using xSynthesis_single a

theorem zSynthesis_eq : BoundaryRecurrence.zSynthesis = HZ.transpose.mulVecLin := by
  apply (Pi.basisFun F2 ZAnchor).ext
  intro a
  simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.transpose_apply] using zSynthesis_single a

/-- Actual matrix ranks for the explicit rectangular model. -/
theorem matrix_ranks : HX.rank = 357 ∧ HZ.rank = 357 := by
  constructor
  · rw [← Matrix.rank_transpose HX, Matrix.rank, ← xSynthesis_eq]
    exact BoundaryRecurrence.xSynthesis_rank
  · rw [← Matrix.rank_transpose HZ, Matrix.rank, ← zSynthesis_eq]
    exact BoundaryRecurrence.zSynthesis_rank

abbrev V := Q → F2

/-- The X row space, in the original physical coordinates. -/
def SX : Submodule F2 V := LinearMap.range HX.transpose.mulVecLin

/-- The orthogonal space of the Z rows, expressed as a parity-check kernel. -/
def ZOrthogonal : Submodule F2 V := LinearMap.ker HZ.mulVecLin

theorem x_mem_zOrthogonal : SX ≤ ZOrthogonal := by
  apply LinearMap.range_le_ker_iff.mpr
  rw [← Matrix.mulVecLin_mul]
  have h : HZ * HX.transpose = 0 := by
    have ht := congrArg Matrix.transpose commutation
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using ht
  rw [h, Matrix.mulVecLin_zero]

theorem SX_finrank : Module.finrank F2 SX = 357 := by
  change Module.finrank F2 (LinearMap.range HX.transpose.mulVecLin) = 357
  rw [← xSynthesis_eq]
  exact BoundaryRecurrence.xSynthesis_rank

theorem ZOrthogonal_finrank : Module.finrank F2 ZOrthogonal = 365 := by
  have h := HZ.mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank F2 (LinearMap.range HZ.mulVecLin) = 357 := matrix_ranks.2
  have hv : Module.finrank F2 V = 722 := by simp [V, Q, Cell]
  change Module.finrank F2 (LinearMap.range HZ.mulVecLin) +
    Module.finrank F2 ZOrthogonal = Module.finrank F2 V at h
  omega

/-- The X row space regarded as a subspace of the orthogonal space of Z. -/
def XInsideZ : Submodule F2 ZOrthogonal := SX.comap ZOrthogonal.subtype

/-- The precise binary quotient of the draft, with dimension eight. -/
theorem quotient_finrank : Module.finrank F2 (ZOrthogonal ⧸ XInsideZ) = 8 := by
  have he := (Submodule.comapSubtypeEquivOfLe x_mem_zOrthogonal).finrank_eq
  have hx : Module.finrank F2 XInsideZ = 357 := he.trans SX_finrank
  have h := XInsideZ.finrank_quotient_add_finrank
  rw [hx, ZOrthogonal_finrank] at h
  exact Nat.add_right_cancel h

/-- Commutation, both actual matrix ranks, and the binary quotient dimension. -/
theorem parameters722 : HX * HZ.transpose = 0 ∧ HX.rank = 357 ∧ HZ.rank = 357 ∧
    Module.finrank F2 (ZOrthogonal ⧸ XInsideZ) = 8 :=
  ⟨commutation, matrix_ranks.1, matrix_ranks.2, quotient_finrank⟩

end QldpcVerification.Planar.Parameters722
