import QldpcVerification.Bicycle.NormalizedShortest
import QldpcVerification.Input.Bicycle454Match
import QldpcVerification.Lattice.Bicycle454Arithmetic

namespace QldpcVerification.Bicycle454
open Module Input Bicycle454Data Bicycle454Model

abbrev code := Bicycle454Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 226 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 226 := matching.rankZ

theorem parameters :
    (454 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 21 ∧ code.DistZ 21 :=
  matching.parameters_of_shortest 21 Lattice.Bicycle454Arithmetic.bound
    Lattice.Bicycle454Arithmetic.shortest_relation

end QldpcVerification.Bicycle454
