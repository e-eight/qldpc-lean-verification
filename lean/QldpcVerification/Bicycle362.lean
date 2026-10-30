import QldpcVerification.Input.Bicycle362Match
import QldpcVerification.Lattice.Bicycle362Arithmetic

namespace QldpcVerification.Bicycle362
open Module Input Bicycle362Data Bicycle362Model

abbrev code := Bicycle362Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 180 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 180 := matching.rankZ

theorem parameters :
    (362 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 19 ∧ code.DistZ 19 :=
  matching.parameters 19 Lattice.Bicycle362Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle362
