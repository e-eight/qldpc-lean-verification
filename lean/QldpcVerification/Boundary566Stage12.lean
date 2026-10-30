import QldpcVerification.Input.Removal566Comm
import QldpcVerification.Input.Removal566RankX
import QldpcVerification.Input.Removal566RankZ

/-! One kernel-certified stage of the reconstructed physical removal sequence. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Stage12
theorem hx_eq : code.HX = matrix hx := rfl
theorem hz_eq : code.HZ = matrix hz := rfl
theorem rankX : finrank (ZMod 2) code.xStab = 274 := by
  apply Nat.le_antisymm
  · exact (finrank_range_le_card (R := ZMod 2) code.HX).trans (by simp)
  · exact RankX.rank_lower
theorem rankZ : finrank (ZMod 2) code.zStab = 274 := by
  apply Nat.le_antisymm
  · exact (finrank_range_le_card (R := ZMod 2) code.HZ).trans (by simp)
  · exact RankZ.rank_lower
end Stage12

end QldpcVerification.Removal566
