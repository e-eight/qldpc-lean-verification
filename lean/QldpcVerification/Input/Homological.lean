import QldpcVerification.Input.MatrixSpec
import QldpcVerification.Coverage

/-! Matrix input as QECLean's chain complex. All semantic bridges are proved here. -/

namespace QldpcVerification.Input.CSSCode

open Matrix Module Quantum.Stabilizer.Homological
open HomologicalCode

set_option maxHeartbeats 0

variable {n mX mZ : ℕ} (C : CSSCode n mX mZ)

def homological : HomologicalCode where
  C0 := Fin mZ
  C1 := Fin n
  C2 := Fin mX
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := C.HZ.mulVecLin
  boundary2 := C.HX.transpose.mulVecLin
  boundary_comp := by
    rw [← Matrix.mulVecLin_mul]
    have ht := congrArg Matrix.transpose C.comm
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
    rw [ht]
    ext x i
    simp
  numQubits := n
  numQubits_eq := Fintype.card_fin n
  edgeEquiv := Equiv.refl _

theorem boundaries_eq : C.homological.boundaries = C.xStab := by
  change LinearMap.range C.HX.transpose.mulVecLin = _
  rw [Matrix.range_mulVecLin]
  rfl

theorem dualBoundary_eq : C.homological.dualBoundary = C.HX.mulVecLin := by
  apply LinearMap.ext
  intro x
  funext i
  change (∑ q, x q * (C.HX.transpose.mulVec (Pi.single i 1)) q) = _
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply]
  exact dotProduct_comm x (C.HX i)

theorem cutMap_eq : C.homological.cutMap = C.HZ.transpose.mulVecLin := by
  apply LinearMap.ext
  intro s
  funext q
  change (∑ j, s j * (C.HZ.mulVec (Pi.single q 1)) j) = _
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  exact dotProduct_comm s (fun j => C.HZ j q)

theorem dualBoundaries_eq : C.homological.dualBoundaries = C.zStab := by
  change LinearMap.range C.homological.cutMap = _
  rw [C.cutMap_eq]
  erw [Matrix.range_mulVecLin]
  rfl

theorem x_logical_iff (x : Vec n) :
    C.IsXLogical x ↔ x ∈ C.homological.cycles ∧ x ∉ C.homological.boundaries := by
  rw [C.boundaries_eq]
  rfl

theorem z_logical_iff (z : Vec n) :
    C.IsZLogical z ↔ z ∈ C.homological.dualCycles ∧ z ∉ C.homological.dualBoundaries := by
  rw [C.dualBoundaries_eq]
  change _ ↔ (C.homological.dualBoundary z = 0 ∧ _)
  rw [C.dualBoundary_eq]
  rfl

theorem rank_nullity (H : Matrix (Fin mX) (Fin n) (ZMod 2)) :
    finrank (ZMod 2) (LinearMap.ker H.mulVecLin) +
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hr : finrank (ZMod 2) (LinearMap.range H.mulVecLin) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) :=
    Matrix.rank_eq_finrank_span_row H
  omega

theorem dimension_bound {k : ℕ}
    (h : n ≤ finrank (ZMod 2) C.xStab + finrank (ZMod 2) C.zStab + k) :
    finrank (ZMod 2) C.homological.cycles ≤ finrank (ZMod 2) C.homological.boundaries + k := by
  rw [C.boundaries_eq]
  have hr := rank_nullity C.HZ
  change finrank (ZMod 2) (LinearMap.ker C.HZ.mulVecLin) ≤ _
  change n ≤ finrank (ZMod 2) C.xStab +
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HZ)) + k at h
  change finrank (ZMod 2) (LinearMap.ker C.HZ.mulVecLin) ≤
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HX)) + k
  change n ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HX)) +
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HZ)) + k at h
  omega

theorem dual_dimension_bound {k : ℕ}
    (h : n ≤ finrank (ZMod 2) C.xStab + finrank (ZMod 2) C.zStab + k) :
    finrank (ZMod 2) C.homological.dualCycles ≤
      finrank (ZMod 2) C.homological.dualBoundaries + k := by
  rw [C.dualBoundaries_eq]
  change finrank (ZMod 2) (LinearMap.ker C.homological.dualBoundary) ≤ _
  rw [C.dualBoundary_eq]
  have hr := rank_nullity C.HX
  change n ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HX)) +
    finrank (ZMod 2) C.zStab + k at h
  change finrank (ZMod 2) (LinearMap.ker C.HX.mulVecLin) ≤
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HZ)) + k
  change n ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HX)) +
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HZ)) + k at h
  omega

end QldpcVerification.Input.CSSCode
