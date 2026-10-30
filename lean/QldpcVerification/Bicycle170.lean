import QldpcVerification.Input.Bicycle170Match
import QldpcVerification.Lattice.Bicycle170Arithmetic

namespace QldpcVerification.Bicycle170
open Module Input Bicycle170Data Bicycle170Model

abbrev code := Bicycle170Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 84 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 84 := matching.rankZ

theorem parameters :
    (170 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 13 ∧ code.DistZ 13 :=
  matching.parameters 13 Lattice.Bicycle170Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle170
