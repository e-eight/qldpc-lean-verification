import QldpcVerification.Planar.Rectangle722Family
import QldpcVerification.Input.Homological
import QldpcVerification.Transport

/-! The explicit rectangular construction as the project's QECLean-backed CSS
matrix type. This file does not identify an external JSON input. -/

namespace QldpcVerification.Rectangle722

open Matrix Module Input

def boolIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def qubits : Planar.Commutation.Q ≃ Fin 722 :=
  (Equiv.prodCongr boolIndex (finProdFinEquiv : Planar.Commutation.Cell ≃ Fin 361)).trans finProdFinEquiv

def xRows : Planar.Commutation.XAnchor ≃ Fin 357 := finProdFinEquiv
def zRows : Planar.Commutation.ZAnchor ≃ Fin 357 := finProdFinEquiv

def code : CSSCode 722 357 357 where
  HX i q := Planar.Commutation.HX (xRows.symm i) (qubits.symm q)
  HZ i q := Planar.Commutation.HZ (zRows.symm i) (qubits.symm q)
  comm := by
    change (Planar.Commutation.HX.submatrix xRows.symm qubits.symm) *
      (Planar.Commutation.HZ.transpose.submatrix qubits.symm zRows.symm) = 0
    rw [Matrix.submatrix_mul_equiv, Planar.Rectangle722Family.commutation]
    rfl

/-- The canonical ordering agrees definitionally with the whole-family model. -/
theorem code_eq_family : code = Planar.RectangleFamily.code 17 17 := rfl

theorem rankX : finrank (ZMod 2) code.xStab = 357 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.rankX 17 17

theorem rankZ : finrank (ZMod 2) code.zStab = 357 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.rankZ 17 17

theorem encoded_qubits :
    722 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 8 := by
  rw [code_eq_family]
  exact Planar.RectangleFamily.encoded_qubits 17 17

theorem x_rows (i : Fin 357) : pull qubits (code.HX i) = Planar.Commutation.HX (xRows.symm i) := by
  ext q
  simp [pull, code]

theorem z_rows (i : Fin 357) : pull qubits (code.HZ i) = Planar.Commutation.HZ (zRows.symm i) := by
  ext q
  simp [pull, code]

theorem x_logical_iff (x : Vec 722) : code.IsXLogical x ↔
    Planar.Commutation.HZ.mulVec (pull qubits x) = 0 ∧
      pull qubits x ∉ Submodule.span (ZMod 2) (Set.range Planar.Commutation.HX) := by
  change (code.HZ.mulVec x = 0 ∧ x ∉ Submodule.span (ZMod 2) (Set.range code.HX)) ↔ _
  rw [kernel_pull_iff qubits code.HZ Planar.Commutation.HZ zRows.symm zRows.symm.surjective z_rows x]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff qubits code.HX Planar.Commutation.HX xRows.symm xRows.symm.surjective x_rows x)).symm

theorem z_logical_iff (z : Vec 722) : code.IsZLogical z ↔
    Planar.Commutation.HX.mulVec (pull qubits z) = 0 ∧
      pull qubits z ∉ Submodule.span (ZMod 2) (Set.range Planar.Commutation.HZ) := by
  change (code.HX.mulVec z = 0 ∧ z ∉ Submodule.span (ZMod 2) (Set.range code.HZ)) ↔ _
  rw [kernel_pull_iff qubits code.HX Planar.Commutation.HX xRows.symm xRows.symm.surjective x_rows z]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff qubits code.HZ Planar.Commutation.HZ zRows.symm zRows.symm.surjective z_rows z)).symm

end QldpcVerification.Rectangle722
