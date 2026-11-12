import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.BicycleEven16FamilyMatch
import QldpcVerification.Lattice.BicycleEven16FamilyArithmetic

namespace QldpcVerification.BicycleEven16Family
open Module Input BicycleEven16FamilyData BicycleEven16FamilyModel

abbrev code := BicycleEven16FamilyModel.code

theorem rankX : finrank (ZMod 2) code.xStab = 7 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 7 := matching.rankZ

theorem parameters :
    (16 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 4 ∧ code.DistZ 4 :=
  matching.parameters_of_shortest 4 Lattice.BicycleEven16FamilyArithmetic.bound
    Lattice.BicycleEven16FamilyArithmetic.shortest_relation

end QldpcVerification.BicycleEven16Family
