import QldpcVerification.Planar.StripFamilyRunCounting

/-!
# Nineteen-slice run-counting compatibility interface

The original definitions and cost structures remain unchanged, including
constructors and projections. Counting, endpoint, and reflection theorems
specialize the family proofs at `N = 16`.
-/

namespace QldpcVerification.Planar.StripRunCounting

open Finset StripCounting

/-- Exactly the forward missing-exit configuration, not an arbitrary slack. -/
def missingForward (w : ℕ → ℕ) : ℕ := if w 16 = 0 ∧ w 18 = 0 then 1 else 0

def missingBackward (w : ℕ → ℕ) : ℕ := if w 0 = 0 ∧ w 2 = 0 then 1 else 0

/-- Local forward hypotheses. `incoming` concerns a long gap preceded by a
short gap, and gives precisely the extra-unit/terminal-feed alternative. -/
structure ForwardCosts (w : ℕ → ℕ) : Prop where
  adjacent : ∀ i, i + 1 < 19 → 1 ≤ w i + w (i + 1)
  branch : ForwardBranch w 19
  long : ∀ a b, a + 3 ≤ b → b < 19 → w a = 0 → w b = 0 → Occupied w a b →
    1 ≤ intervalSum (excess w) (a + 1) b
  incoming : ∀ a b, 2 ≤ a → a + 3 ≤ b → b < 19 →
    w (a - 2) = 0 → w a = 0 → w b = 0 → Occupied w a b →
    2 ≤ intervalSum (excess w) (a + 1) b ∨ 3 ≤ w (a - 1)

/-- Backward local hypotheses in the original, increasing index convention.
The incoming short gap is on the right; its terminal middle is `b+1`. -/
structure BackwardCosts (w : ℕ → ℕ) : Prop where
  adjacent : ∀ i, i + 1 < 19 → 1 ≤ w i + w (i + 1)
  branch : BackwardBranch w 19
  long : ∀ a b, a + 3 ≤ b → b < 19 → w a = 0 → w b = 0 → Occupied w a b →
    1 ≤ intervalSum (excess w) (a + 1) b
  incoming : ∀ a b, b + 2 < 19 → a + 3 ≤ b →
    w (b + 2) = 0 → w a = 0 → w b = 0 → Occupied w a b →
    2 ≤ intervalSum (excess w) (a + 1) b ∨ 3 ≤ w (b + 1)

private theorem forward_family {w : ℕ → ℕ} (costs : ForwardCosts w) :
    StripFamilyRunCounting.ForwardCosts 16 w :=
  ⟨costs.adjacent, costs.branch, costs.long, costs.incoming⟩

private theorem backward_family {w : ℕ → ℕ} (costs : BackwardCosts w) :
    StripFamilyRunCounting.BackwardCosts 16 w :=
  ⟨costs.adjacent, costs.branch, costs.long, costs.incoming⟩

theorem missingForward_le_one (w : ℕ → ℕ) : missingForward w ≤ 1 := by
  exact StripFamilyRunCounting.missingForward_le_one (N := 16) w

theorem short_excess (w : ℕ → ℕ) (a : ℕ) (ha : w a = 0) :
    intervalSum (excess w) a (a + 2) = w (a + 1) - 1 := by
  exact StripFamilyRunCounting.short_excess w a ha

theorem zero_suffix_budget (w : ℕ → ℕ) (costs : ForwardCosts w)
    (a : ℕ) (ha : a < 19) (ha0 : w a = 0) :
    (intervalSum (zeroIndicator w) a 19 ≤ intervalSum (excess w) a 19 +
      1 + missingForward w) ∧
    (2 ≤ a → w (a - 2) = 0 →
      intervalSum (zeroIndicator w) a 19 ≤ intervalSum (excess w) a 19 +
        missingForward w + (w (a - 1) - 2)) := by
  exact StripFamilyRunCounting.zero_suffix_budget (N := 16) w (forward_family costs) a ha ha0

theorem forward_excess_budget (w : ℕ → ℕ) (costs : ForwardCosts w) :
    intervalSum (zeroIndicator w) 0 19 ≤ intervalSum (excess w) 0 19 +
      1 + missingForward w := by
  exact StripFamilyRunCounting.forward_excess_budget (N := 16) w (forward_family costs)

theorem forward_weight_with_endpoint (w : ℕ → ℕ) (costs : ForwardCosts w) :
    18 ≤ intervalSum w 0 19 + missingForward w := by
  exact StripFamilyRunCounting.forward_weight_with_endpoint (N := 16) w (forward_family costs)

theorem weight_ge_seventeen_forward (w : ℕ → ℕ) (costs : ForwardCosts w) :
    17 ≤ intervalSum w 0 19 := by
  exact StripFamilyRunCounting.weight_ge_length_sub_two_forward (N := 16) w (forward_family costs)

theorem weight_ge_eighteen_forward (w : ℕ → ℕ) (costs : ForwardCosts w)
    (hexit : ¬ (w 16 = 0 ∧ w 18 = 0)) : 18 ≤ intervalSum w 0 19 := by
  exact StripFamilyRunCounting.weight_ge_length_sub_one_forward (N := 16) w (forward_family costs) hexit

/-- Reverse precisely the original nineteen indices. -/
def reverseWeights (w : ℕ → ℕ) (i : ℕ) : ℕ := w (18 - i)

theorem reverse_interval (f : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ 19) :
    intervalSum (reverseWeights f) a b = intervalSum f (19 - b) (19 - a) := by
  exact StripFamilyRunCounting.reverse_interval (N := 16) f hab hb

theorem reverse_total (w : ℕ → ℕ) :
    intervalSum (reverseWeights w) 0 19 = intervalSum w 0 19 := by
  exact StripFamilyRunCounting.reverse_total (N := 16) w

theorem reverse_excess_total (w : ℕ → ℕ) :
    intervalSum (excess (reverseWeights w)) 0 19 = intervalSum (excess w) 0 19 := by
  exact StripFamilyRunCounting.reverse_excess_total (N := 16) w

theorem reverse_zero_total (w : ℕ → ℕ) :
    intervalSum (zeroIndicator (reverseWeights w)) 0 19 =
      intervalSum (zeroIndicator w) 0 19 := by
  exact StripFamilyRunCounting.reverse_zero_total (N := 16) w

theorem missingForward_reverse (w : ℕ → ℕ) :
    missingForward (reverseWeights w) = missingBackward w := by
  exact StripFamilyRunCounting.missingForward_reverse (N := 16) w

theorem reverse_occupied (w : ℕ → ℕ) {a b : ℕ} (hab : a < b) (hb : b < 19)
    (hocc : Occupied (reverseWeights w) a b) : Occupied w (18 - b) (18 - a) := by
  exact StripFamilyRunCounting.reverse_occupied (N := 16) w hab hb hocc

theorem reverse_gap_excess (w : ℕ → ℕ) {a b : ℕ} (hab : a < b) (hb : b < 19) :
    intervalSum (excess (reverseWeights w)) (a + 1) b =
      intervalSum (excess w) (18 - b + 1) (18 - a) := by
  exact StripFamilyRunCounting.reverse_gap_excess (N := 16) w hab hb

theorem backwardCosts_reverse (w : ℕ → ℕ) (costs : BackwardCosts w) :
    ForwardCosts (reverseWeights w) := by
  have h := StripFamilyRunCounting.backwardCosts_reverse (N := 16) w (backward_family costs)
  exact ⟨h.adjacent, h.branch, h.long, h.incoming⟩

theorem backward_excess_budget (w : ℕ → ℕ) (costs : BackwardCosts w) :
    intervalSum (zeroIndicator w) 0 19 ≤ intervalSum (excess w) 0 19 +
      1 + missingBackward w := by
  exact StripFamilyRunCounting.backward_excess_budget (N := 16) w (backward_family costs)

theorem backward_weight_with_endpoint (w : ℕ → ℕ) (costs : BackwardCosts w) :
    18 ≤ intervalSum w 0 19 + missingBackward w := by
  exact StripFamilyRunCounting.backward_weight_with_endpoint (N := 16) w (backward_family costs)

theorem weight_ge_seventeen_backward (w : ℕ → ℕ) (costs : BackwardCosts w) :
    17 ≤ intervalSum w 0 19 := by
  exact StripFamilyRunCounting.weight_ge_length_sub_two_backward (N := 16) w (backward_family costs)

theorem weight_ge_eighteen_backward (w : ℕ → ℕ) (costs : BackwardCosts w)
    (hexit : ¬ (w 0 = 0 ∧ w 2 = 0)) : 18 ≤ intervalSum w 0 19 := by
  exact StripFamilyRunCounting.weight_ge_length_sub_one_backward (N := 16) w (backward_family costs) hexit

end QldpcVerification.Planar.StripRunCounting
