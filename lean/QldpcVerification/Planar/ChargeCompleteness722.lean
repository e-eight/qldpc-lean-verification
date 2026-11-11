import QldpcVerification.Planar.BoundaryRealization
import QldpcVerification.Planar.CycleSpaces722
import QldpcVerification.Planar.SyndromeMatrix722
import QldpcVerification.Planar.StabilizerCharge722

/-! Complete logical charges for the actual explicit rectangular matrices.
No external input recognition is asserted. -/
namespace QldpcVerification.Planar.ChargeCompleteness722

open Module Commutation CycleSpaces722

noncomputable section

abbrev A := ChargeAlgebra.A
abbrev Poly := BulkExactness.Bivariate

def xAmbientCharge : V →ₗ[F2] A :=
  BoundaryResidue.leftX.comp (BoundaryPolynomial.extract.comp Syndrome722.fullSyndrome)

def xCharge : xCycles →ₗ[F2] A := xAmbientCharge.comp xCycles.subtype

theorem xCharge_eq_low (w : xCycles) :
    xCharge w = CutCharge.lowCharge (Syndrome722.encode w.val).1
      (Syndrome722.encode w.val).2 := by
  exact BoundaryPolynomial.low_residue_extract (Syndrome722.fullSyndrome w.val)
    (Syndrome722.fullSyndrome_inSquare w.val)
    (SyndromeMatrix722.x_cycle_coeff w.val w.property)

theorem xAmbientCharge_rows (a : XAnchor) : xAmbientCharge (HX a) = 0 := by
  have he := xCharge_eq_low (⟨HX a, StabilizerCharge722.HX_cycle a⟩ : xCycles)
  exact he.trans (StabilizerCharge722.HX_lowCharge a)

theorem xAmbientCharge_stabilizers : xStab ≤ LinearMap.ker xAmbientCharge := by
  rw [xStab_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact xAmbientCharge_rows a

theorem x_syndrome_kernel_le : LinearMap.ker Syndrome722.fullSyndrome ≤ xCycles := by
  intro w hw
  apply (SyndromeMatrix722.x_cycle_iff w).mpr
  intro i _ _
  change Syndrome722.fullSyndrome w = 0 at hw
  rw [hw]
  simp

theorem x_complete : Function.Surjective xCharge ∧ xBoundaries = LinearMap.ker xCharge := by
  apply BoundaryRealization.complete Syndrome722.fullSyndrome xCycles xBoundaries
    BoundaryResidue.totalX BoundaryResidue.leftX xCycles_finrank xBoundaries_finrank
    Syndrome722.fullSyndrome_kernel_finrank x_syndrome_kernel_le
    Syndrome722.fullSyndrome_inSquare
    (fun w hw => SyndromeMatrix722.x_cycle_coeff w hw)
  · intro w hw
    rw [BoundaryPolynomial.residue_extract _ (Syndrome722.fullSyndrome_inSquare w)
      (SyndromeMatrix722.x_cycle_coeff w hw)]
    exact CutCharge.residue_syndrome _ _
  · exact BoundaryResidue.totalX_kernel_finrank
  · exact BoundaryResidue.split_liftX
  · intro b hb
    exact xAmbientCharge_stabilizers hb

theorem x_detects (w : V) (hc : HZ.mulVec w = 0) (hb : w ∉ xStab) :
    CutCharge.lowCharge (Syndrome722.encode w).1 (Syndrome722.encode w).2 ≠ 0 := by
  intro hz
  have hc0 : xCharge (⟨w, hc⟩ : xCycles) = 0 := (xCharge_eq_low _).trans hz
  have hm : (⟨w, hc⟩ : xCycles) ∈ LinearMap.ker xCharge := hc0
  rw [← x_complete.2] at hm
  exact hb hm

/-- Full syndrome in the reflected, swapped orientation of the Z proof. -/
def zSyndrome : V →ₗ[F2] Poly :=
  BulkExactness.swap.toLinearMap.comp
    (Syndrome722.fullSyndrome.comp SyndromeMatrix722.reflectPhysical.toLinearMap)

def zKernelEquiv : LinearMap.ker zSyndrome ≃ₗ[F2]
    LinearMap.ker Syndrome722.fullSyndrome where
  toFun w := ⟨SyndromeMatrix722.reflectPhysical w.val, by
    apply BulkExactness.swap.injective
    simpa only [map_zero] using w.property⟩
  invFun w := ⟨SyndromeMatrix722.reflectPhysical w.val, by
    change BulkExactness.swap
      (Syndrome722.fullSyndrome (SyndromeMatrix722.reflectPhysical
        (SyndromeMatrix722.reflectPhysical w.val))) = 0
    rw [SyndromeMatrix722.reflectPhysical_involutive, w.property, map_zero]⟩
  left_inv w := by
    apply Subtype.ext
    exact SyndromeMatrix722.reflectPhysical_involutive w.val
  right_inv w := by
    apply Subtype.ext
    exact SyndromeMatrix722.reflectPhysical_involutive w.val
  map_add' w v := by ext q; rfl
  map_smul' a w := by ext q; rfl

theorem zSyndrome_kernel_finrank : finrank F2 (LinearMap.ker zSyndrome) = 289 :=
  zKernelEquiv.finrank_eq.trans Syndrome722.fullSyndrome_kernel_finrank

theorem zSyndrome_inSquare (w : V) : BulkExactness.InSquare 20 (zSyndrome w) := by
  have hp := Syndrome722.fullSyndrome_inSquare (SyndromeMatrix722.reflectPhysical w)
  refine ⟨hp.2, ?_⟩
  change (BulkExactness.swap (BulkExactness.swap
    (Syndrome722.fullSyndrome (SyndromeMatrix722.reflectPhysical w)))).natDegree ≤ 20
  simpa only [BulkExactness.swap, Polynomial.Bivariate.swap_swap_apply] using hp.1

theorem z_syndrome_kernel_le : LinearMap.ker zSyndrome ≤ zCycles := by
  intro w hw
  apply (SyndromeMatrix722.z_cycle_iff w).mpr
  intro i _ _
  change zSyndrome w = 0 at hw
  change (zSyndrome w).coeff i = 0
  rw [hw]
  simp

def zAmbientCharge : V →ₗ[F2] A :=
  BoundaryResidue.leftZ.comp (BoundaryPolynomial.extract.comp zSyndrome)

def zCharge : zCycles →ₗ[F2] A := zAmbientCharge.comp zCycles.subtype

theorem zCharge_eq_low (w : zCycles) :
    zCharge w = CutCharge.lowColumnCharge
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical w.val)).1
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical w.val)).2 := by
  exact BoundaryPolynomial.low_columnResidue_extract (zSyndrome w.val)
    (zSyndrome_inSquare w.val) (SyndromeMatrix722.z_cycle_coeff w.val w.property)

theorem zAmbientCharge_rows (a : ZAnchor) : zAmbientCharge (HZ a) = 0 := by
  have he := zCharge_eq_low (⟨HZ a, StabilizerCharge722.HZ_cycle a⟩ : zCycles)
  exact he.trans (StabilizerCharge722.HZ_lowColumnCharge a)

theorem zAmbientCharge_stabilizers : zStab ≤ LinearMap.ker zAmbientCharge := by
  rw [zStab_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact zAmbientCharge_rows a

theorem z_complete : Function.Surjective zCharge ∧ zBoundaries = LinearMap.ker zCharge := by
  apply BoundaryRealization.complete zSyndrome zCycles zBoundaries
    BoundaryResidue.totalZ BoundaryResidue.leftZ zCycles_finrank zBoundaries_finrank
    zSyndrome_kernel_finrank z_syndrome_kernel_le zSyndrome_inSquare
    (fun w hw => SyndromeMatrix722.z_cycle_coeff w hw)
  · intro w hw
    rw [BoundaryPolynomial.columnResidue_extract _ (zSyndrome_inSquare w)
      (SyndromeMatrix722.z_cycle_coeff w hw)]
    change CutCharge.columnResidue (BulkExactness.swap
      (Syndrome722.fullSyndrome (SyndromeMatrix722.reflectPhysical w))) = 0
    rw [CutCharge.columnResidue_swap]
    exact CutCharge.residue_syndrome _ _
  · exact BoundaryResidue.totalZ_kernel_finrank
  · exact BoundaryResidue.split_liftZ
  · intro b hb
    exact zAmbientCharge_stabilizers hb

theorem z_detects (w : V) (hc : HX.mulVec w = 0) (hb : w ∉ zStab) :
    CutCharge.lowColumnCharge
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical w)).1
      (Syndrome722.encode (SyndromeMatrix722.reflectPhysical w)).2 ≠ 0 := by
  intro hz
  have hc0 : zCharge (⟨w, hc⟩ : zCycles) = 0 := (zCharge_eq_low _).trans hz
  have hm : (⟨w, hc⟩ : zCycles) ∈ LinearMap.ker zCharge := hc0
  rw [← z_complete.2] at hm
  exact hb hm

end
end QldpcVerification.Planar.ChargeCompleteness722
