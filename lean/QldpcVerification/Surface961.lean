import QldpcVerification.Input.Surface961Match

namespace QldpcVerification.Surface961

local instance : Fact (Odd 31) := ⟨by decide⟩
local instance : Fact (3 ≤ 31) := ⟨by decide⟩

abbrev code := certificate.code

theorem parameters :
    (961 - Module.finrank (ZMod 2) code.xStab - Module.finrank (ZMod 2) code.zStab = 1) ∧
      code.DistX 31 ∧ code.DistZ 31 := certificate.parameters

end QldpcVerification.Surface961
