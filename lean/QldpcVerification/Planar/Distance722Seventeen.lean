import QldpcVerification.Planar.StripRunRecurrence
import QldpcVerification.Planar.PhysicalStrips722

/-! Stronger analytic bounds from local cancellation and symbolic gap counting. -/
namespace QldpcVerification.Planar.Distance722Seventeen

open Commutation CycleSpaces722 PhysicalStrips722

theorem x_lower (w : V) (hc : HZ.mulVec w = 0) (hb : w ∉ xStab) :
    17 ≤ hammingNorm w := by
  have h := StripRunRecurrence.forward_weight_ge_seventeen (forwardA w) (forwardB w)
    (forward_recurrence w hc)
    (fun i hi => forward_adjacent w hc hb i (by omega))
  simpa only [forward_weight] using h

theorem z_lower (w : V) (hc : HX.mulVec w = 0) (hb : w ∉ zStab) :
    17 ≤ hammingNorm w := by
  have h := StripRunRecurrence.backward_weight_ge_seventeen (backwardA w) (backwardB w)
    (backward_recurrence w hc)
    (fun i hi => backward_adjacent w hc hb i (by omega))
  simpa only [backward_weight] using h

end QldpcVerification.Planar.Distance722Seventeen
