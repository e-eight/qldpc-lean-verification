import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle110Match
import QldpcVerification.Lattice.Bicycle110Arithmetic

namespace QldpcVerification.Bicycle110
open Module Input Bicycle110Data Bicycle110Model

abbrev code := Bicycle110Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 54 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 54 := matching.rankZ

theorem parameters :
    (110 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 10 ∧ code.DistZ 10 :=
  matching.parameters_of_shortest 10 Lattice.Bicycle110Arithmetic.bound
    Lattice.Bicycle110Arithmetic.shortest_relation

end QldpcVerification.Bicycle110
