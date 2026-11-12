import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle562FamilyMatch
import QldpcVerification.Lattice.Bicycle562FamilyArithmetic

namespace QldpcVerification.Bicycle562Family
open Module Input Bicycle562FamilyData Bicycle562FamilyModel

abbrev code := Bicycle562FamilyModel.code

theorem rankX : finrank (ZMod 2) code.xStab = 280 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 280 := matching.rankZ

theorem parameters :
    (562 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 23 ∧ code.DistZ 23 :=
  matching.parameters_of_shortest 23 Lattice.Bicycle562FamilyArithmetic.bound
    Lattice.Bicycle562FamilyArithmetic.shortest_relation

end QldpcVerification.Bicycle562Family
