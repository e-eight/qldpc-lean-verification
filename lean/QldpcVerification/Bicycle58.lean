import QldpcVerification.Input.Bicycle58Match
import QldpcVerification.Lattice.Bicycle58Arithmetic

namespace QldpcVerification.Bicycle58
open Module Input Bicycle58Data Bicycle58Model

abbrev code := Bicycle58Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 28 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 28 := matching.rankZ

theorem parameters :
    (58 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 7 ∧ code.DistZ 7 :=
  matching.parameters 7 Lattice.Bicycle58Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle58
