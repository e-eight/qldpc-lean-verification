import QldpcVerification.Input.Bicycle226Match
import QldpcVerification.Lattice.Bicycle226Arithmetic

namespace QldpcVerification.Bicycle226
open Module Input Bicycle226Data Bicycle226Model

abbrev code := Bicycle226Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 112 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 112 := matching.rankZ

theorem parameters :
    (226 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 15 ∧ code.DistZ 15 :=
  matching.parameters 15 Lattice.Bicycle226Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle226
