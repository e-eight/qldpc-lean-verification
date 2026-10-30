import QldpcVerification.Input.BicycleEvenStep16Match
import QldpcVerification.Lattice.BicycleEvenStep16Arithmetic

namespace QldpcVerification.BicycleEvenStep16
open Module Input BicycleEvenStep16Data BicycleEvenStep16Model

abbrev code := BicycleEvenStep16Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 7 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 7 := matching.rankZ

theorem parameters :
    (16 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 3 ∧ code.DistZ 3 :=
  matching.parameters 3 Lattice.BicycleEvenStep16Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.BicycleEvenStep16
