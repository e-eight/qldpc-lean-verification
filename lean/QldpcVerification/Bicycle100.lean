import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle100Match
import QldpcVerification.Lattice.Bicycle100Arithmetic

namespace QldpcVerification.Bicycle100
open Module Input Bicycle100Data Bicycle100Model

abbrev code := Bicycle100Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 49 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 49 := matching.rankZ

theorem parameters :
    (100 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 10 ∧ code.DistZ 10 :=
  matching.parameters_of_shortest 10 Lattice.Bicycle100Arithmetic.bound
    Lattice.Bicycle100Arithmetic.shortest_relation

end QldpcVerification.Bicycle100
