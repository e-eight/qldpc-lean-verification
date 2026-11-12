import QldpcVerification.Planar.Commutation
import QldpcVerification.Planar.RectangleFamilyDistance

/-! The existing 722-coordinate model is literally the `(17,17)` family member.
These identities unfold the sparse row formulas and the finite index sizes;
they perform no matrix enumeration and use no charge-specific distance result. -/

namespace QldpcVerification.Planar.Rectangle722Family

theorem HX_eq : Commutation.HX = RectangleFamily.HX 17 17 := rfl

theorem HZ_eq : Commutation.HZ = RectangleFamily.HZ 17 17 := rfl

theorem commutation : Commutation.HX * Commutation.HZ.transpose = 0 := by
  rw [HX_eq, HZ_eq]
  exact RectangleFamily.commutation 17 17

end QldpcVerification.Planar.Rectangle722Family
