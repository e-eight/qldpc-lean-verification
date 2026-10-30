import QldpcVerification.Input.Bicycle122Match
import QldpcVerification.Lattice.Bicycle122Arithmetic

namespace QldpcVerification.Bicycle122
open Module Input Bicycle122Data Bicycle122Model

abbrev code := Bicycle122Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 60 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 60 := matching.rankZ

theorem parameters :
    (122 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 11 ∧ code.DistZ 11 :=
  matching.parameters 11 Lattice.Bicycle122Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle122
