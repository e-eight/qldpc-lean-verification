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
  matching.parameters 9 Lattice.Bicycle82Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle82
