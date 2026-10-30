import QldpcVerification.Input.Bicycle346Match
import QldpcVerification.Lattice.Bicycle346Arithmetic

namespace QldpcVerification.Bicycle346
open Module Input Bicycle346Data Bicycle346Model

abbrev code := Bicycle346Model.code

theorem rankX : finrank (ZMod 2) code.xStab = 172 := matching.rankX
theorem rankZ : finrank (ZMod 2) code.zStab = 172 := matching.rankZ

theorem parameters :
    (346 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 18 ∧ code.DistZ 18 :=
  matching.parameters 18 Lattice.Bicycle346Arithmetic.bound
    ⟨_, wx_logical, wx_weight⟩ ⟨_, wz_logical, wz_weight⟩

end QldpcVerification.Bicycle346
