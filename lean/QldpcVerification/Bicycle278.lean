import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle278Match
import QldpcVerification.Lattice.Bicycle278Arithmetic

namespace QldpcVerification.Bicycle278
open Module Input Bicycle278Data Bicycle278Model

abbrev code := Bicycle278Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 138 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 138 := matching.rankZ

theorem parameters :
    (278 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 16 ∧ code.DistZ 16 :=
  matching.parameters_of_shortest 16 Lattice.Bicycle278Arithmetic.bound
    Lattice.Bicycle278Arithmetic.shortest_relation

end QldpcVerification.Bicycle278
