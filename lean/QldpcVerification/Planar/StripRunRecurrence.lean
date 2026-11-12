import QldpcVerification.Planar.StripRecurrence
import QldpcVerification.Planar.StripRunCounting
import QldpcVerification.Planar.StripFamilyRunRecurrence

/-!
# Nineteen-slice run-recurrence compatibility interface

These declarations retain the original hypotheses and conclusions while
specializing the arbitrary-length polynomial theory at `N = 16`.
-/

namespace QldpcVerification.Planar.StripRunRecurrence

open StripLocal StripCounting StripRecurrence StripRunLocal StripRunCounting
open scoped CharTwo

noncomputable section

theorem three_excess (w : ℕ → ℕ) (hc : GapCosts w 19) (k : ℕ)
    (hk : k + 3 < 19) (h0 : w k = 0) (h3 : w (k + 3) = 0)
    (ho : Occupied w k (k + 3)) : 2 ≤ intervalSum (excess w) (k + 1) (k + 3) := by
  exact StripFamilyRunRecurrence.three_excess (N := 16) w hc k hk h0 h3 ho

theorem forward_long {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b)
    (l r : ℕ) (hlr : l + 3 ≤ r) (hr : r < 19)
    (h0 : weight a b l = 0) (hR : weight a b r = 0)
    (ho : Occupied (weight a b) l r) :
    1 ≤ intervalSum (excess (weight a b)) (l + 1) r := by
  exact StripFamilyRunRecurrence.forward_long (N := 16) hf ha l r hlr hr h0 hR ho

theorem backward_long {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b)
    (l r : ℕ) (hlr : l + 3 ≤ r) (hr : r < 19)
    (h0 : weight a b l = 0) (hR : weight a b r = 0)
    (ho : Occupied (weight a b) l r) :
    1 ≤ intervalSum (excess (weight a b)) (l + 1) r := by
  exact StripFamilyRunRecurrence.backward_long (N := 16) hf ha l r hlr hr h0 hR ho

theorem forward_incoming {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b)
    (l r : ℕ) (hl : 2 ≤ l) (hlr : l + 3 ≤ r) (hr : r < 19)
    (hprev : weight a b (l - 2) = 0) (h0 : weight a b l = 0)
    (hR : weight a b r = 0) (ho : Occupied (weight a b) l r) :
    2 ≤ intervalSum (excess (weight a b)) (l + 1) r ∨ 3 ≤ weight a b (l - 1) := by
  exact StripFamilyRunRecurrence.forward_incoming (N := 16) hf ha l r hl hlr hr hprev h0 hR ho

theorem backward_incoming {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b)
    (l r : ℕ) (hr : r + 2 < 19) (hlr : l + 3 ≤ r)
    (hnext : weight a b (r + 2) = 0) (h0 : weight a b l = 0)
    (hR : weight a b r = 0) (ho : Occupied (weight a b) l r) :
    2 ≤ intervalSum (excess (weight a b)) (l + 1) r ∨ 3 ≤ weight a b (r + 1) := by
  exact StripFamilyRunRecurrence.backward_incoming (N := 16) hf ha l r hr hlr hnext h0 hR ho

theorem forward_costs {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    ForwardCosts (weight a b) := by
  have h := StripFamilyRunRecurrence.forward_costs (N := 16) hf ha
  exact ⟨h.adjacent, h.branch, h.long, h.incoming⟩

theorem backward_costs {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    BackwardCosts (weight a b) := by
  have h := StripFamilyRunRecurrence.backward_costs (N := 16) hf ha
  exact ⟨h.adjacent, h.branch, h.long, h.incoming⟩

theorem forward_weight_ge_seventeen (a b : ℕ → P) (hf : Forward a b) (ha : Adjacent a b) :
    17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  exact StripFamilyRunRecurrence.forward_weight_ge_length_sub_two (N := 16) a b hf ha

theorem backward_weight_ge_seventeen (a b : ℕ → P) (hf : Backward a b) (ha : Adjacent a b) :
    17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  exact StripFamilyRunRecurrence.backward_weight_ge_length_sub_two (N := 16) a b hf ha

theorem forward_weight_ge_eighteen (a b : ℕ → P) (hf : Forward a b) (ha : Adjacent a b)
    (hexit : ¬ (weight a b 16 = 0 ∧ weight a b 18 = 0)) :
    18 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  exact StripFamilyRunRecurrence.forward_weight_ge_length_sub_one (N := 16) a b hf ha hexit

theorem backward_weight_ge_eighteen (a b : ℕ → P) (hf : Backward a b) (ha : Adjacent a b)
    (hexit : ¬ (weight a b 0 = 0 ∧ weight a b 2 = 0)) :
    18 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  exact StripFamilyRunRecurrence.backward_weight_ge_length_sub_one (N := 16) a b hf ha hexit

theorem weight_ge_seventeen (a b : ℕ → P) (hf : Forward a b ∨ Backward a b)
    (ha : Adjacent a b) : 17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  exact StripFamilyRunRecurrence.weight_ge_length_sub_two (N := 16) a b hf ha

end
end QldpcVerification.Planar.StripRunRecurrence
