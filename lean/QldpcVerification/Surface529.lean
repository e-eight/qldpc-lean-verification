import QldpcVerification.Input.Surface529Match

namespace QldpcVerification.Surface529

local instance : Fact (Odd 23) := ⟨by decide⟩
local instance : Fact (3 ≤ 23) := ⟨by decide⟩

abbrev code := certificate.code

theorem parameters :
    (529 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 1) ∧
      code.DistX 23 ∧ code.DistZ 23 := certificate.parameters

end QldpcVerification.Surface529
