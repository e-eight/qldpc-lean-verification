import QldpcVerification.Planar.Parameters722
import QldpcVerification.Planar.Syndrome722

/-! Both physical sector cycle and stabilizer spaces of the explicit rectangle. -/
namespace QldpcVerification.Planar.CycleSpaces722

open Commutation Module Matrix

abbrev V := Q → F2

def xCycles : Submodule F2 V := LinearMap.ker HZ.mulVecLin
def zCycles : Submodule F2 V := LinearMap.ker HX.mulVecLin
def xStab : Submodule F2 V := LinearMap.range HX.transpose.mulVecLin
def zStab : Submodule F2 V := LinearMap.range HZ.transpose.mulVecLin

theorem xStab_le : xStab ≤ xCycles := Parameters722.x_mem_zOrthogonal

theorem zStab_le : zStab ≤ zCycles := by
  rintro _ ⟨a, rfl⟩
  change HX.mulVec (HZ.transpose.mulVec a) = 0
  rw [Matrix.mulVec_mulVec, commutation]
  simp

theorem xStab_finrank : finrank F2 xStab = 357 := Parameters722.SX_finrank

theorem zStab_finrank : finrank F2 zStab = 357 := by
  change HZ.transpose.rank = 357
  rw [Matrix.rank_transpose]
  exact Parameters722.matrix_ranks.2

theorem xCycles_finrank : finrank F2 xCycles = 365 := Parameters722.ZOrthogonal_finrank

theorem zCycles_finrank : finrank F2 zCycles = 365 := by
  have hr := LinearMap.finrank_range_add_finrank_ker HX.mulVecLin
  have hd : finrank F2 V = 722 := Syndrome722.physicalV_finrank
  have hm : finrank F2 (LinearMap.range HX.mulVecLin) = 357 :=
    Parameters722.matrix_ranks.1
  change finrank F2 (LinearMap.range HX.mulVecLin) + finrank F2 zCycles = finrank F2 V at hr
  rw [hd, hm] at hr
  omega

def xBoundaries : Submodule F2 xCycles := xStab.comap xCycles.subtype
def zBoundaries : Submodule F2 zCycles := zStab.comap zCycles.subtype

theorem xBoundaries_finrank : finrank F2 xBoundaries = 357 :=
  (Submodule.comapSubtypeEquivOfLe xStab_le).finrank_eq.trans xStab_finrank

theorem zBoundaries_finrank : finrank F2 zBoundaries = 357 :=
  (Submodule.comapSubtypeEquivOfLe zStab_le).finrank_eq.trans zStab_finrank

theorem xStab_eq_span : xStab = Submodule.span F2 (Set.range HX) := by
  exact Matrix.range_mulVecLin HX.transpose

theorem zStab_eq_span : zStab = Submodule.span F2 (Set.range HZ) := by
  exact Matrix.range_mulVecLin HZ.transpose

end QldpcVerification.Planar.CycleSpaces722
