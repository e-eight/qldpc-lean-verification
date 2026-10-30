import QldpcVerification.Input.Bicycle262LatticeMatch
import QldpcVerification.Lattice.Bicycle262LatticeArithmetic

namespace QldpcVerification.Bicycle262Lattice
open Module Input Bicycle262LatticeData Bicycle262LatticeModel

abbrev code := Bicycle262LatticeModel.code

theorem rankX : finrank (ZMod 2) code.xStab = 130 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 130 := matching.rankZ

theorem parameters :
    (262 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 15 ∧ code.DistZ 15 :=
  matching.parameters 15 Lattice.Bicycle262LatticeArithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle262Lattice
