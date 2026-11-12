import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle422Match
import QldpcVerification.Lattice.Bicycle422Arithmetic

namespace QldpcVerification.Bicycle422
open Module Input Bicycle422Data Bicycle422Model

abbrev code := Bicycle422Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 210 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 210 := matching.rankZ

theorem parameters :
    (422 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 20 ∧ code.DistZ 20 :=
  matching.parameters_of_shortest 20 Lattice.Bicycle422Arithmetic.bound
    Lattice.Bicycle422Arithmetic.shortest_relation

end QldpcVerification.Bicycle422
