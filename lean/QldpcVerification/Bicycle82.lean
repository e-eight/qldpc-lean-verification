import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle82Match
import QldpcVerification.Lattice.Bicycle82Arithmetic

namespace QldpcVerification.Bicycle82
open Module Input Bicycle82Data Bicycle82Model

abbrev code := Bicycle82Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 40 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 40 := matching.rankZ

theorem parameters :
    (82 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 9 ∧ code.DistZ 9 :=
  matching.parameters_of_shortest 9 Lattice.Bicycle82Arithmetic.bound
    Lattice.Bicycle82Arithmetic.shortest_relation

end QldpcVerification.Bicycle82
