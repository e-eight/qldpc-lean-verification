import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle298Match
import QldpcVerification.Lattice.Bicycle298Arithmetic

namespace QldpcVerification.Bicycle298
open Module Input Bicycle298Data Bicycle298Model

abbrev code := Bicycle298Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 148 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 148 := matching.rankZ

theorem parameters :
    (298 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 17 ∧ code.DistZ 17 :=
  matching.parameters_of_shortest 17 Lattice.Bicycle298Arithmetic.bound
    Lattice.Bicycle298Arithmetic.shortest_relation

end QldpcVerification.Bicycle298
