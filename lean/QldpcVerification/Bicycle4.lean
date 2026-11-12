import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle4Match
import QldpcVerification.Lattice.Bicycle4Arithmetic

namespace QldpcVerification.Bicycle4
open Module Input Bicycle4Data Bicycle4Model

abbrev code := Bicycle4Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 1 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 1 := matching.rankZ

theorem parameters :
    (4 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 2 ∧ code.DistZ 2 :=
  matching.parameters_of_shortest 2 Lattice.Bicycle4Arithmetic.bound
    Lattice.Bicycle4Arithmetic.shortest_relation

end QldpcVerification.Bicycle4
