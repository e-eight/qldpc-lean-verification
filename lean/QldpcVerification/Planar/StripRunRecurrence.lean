import QldpcVerification.Planar.StripRecurrence
import QldpcVerification.Planar.StripRunLocal
import QldpcVerification.Planar.StripRunCounting

/-!
# Actual polynomial recurrences supply the run-counting hypotheses

Uses exactly StripRecurrence.Forward/Backward and Adjacent on indices 0..18.
Every local cost is derived; no gap budget or feed-weight assumption is added.
The backward adapter uses the original indices and its own polynomial equations.
No degree restriction, quotient, physical-model hypothesis, or enumeration.
Author source checks only; no local Lean run. Root capped replay is required.
-/

namespace QldpcVerification.Planar.StripRunRecurrence

open StripLocal StripCounting StripRecurrence StripRunLocal StripRunCounting
open scoped CharTwo

noncomputable section

private theorem three_sum (w : ℕ → ℕ) (k : ℕ) :
    intervalSum w k (k + 3) = w k + w (k + 1) + w (k + 2) := by
  unfold intervalSum
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp [Finset.sum_range_succ]

/-- Translate an actual mass lower bound to excess on an occupied interval. -/
private theorem excess_of_mass (w : ℕ → ℕ) (l r c : ℕ)
    (ho : ∀ i, l ≤ i → i < r → 0 < w i)
    (hm : (r - l) + c ≤ intervalSum w l r) :
    c ≤ intervalSum (excess w) l r := by
  have hid := occupied_mass w ho
  omega

/-- Every length-three gap already carries two excess units. -/
theorem three_excess (w : ℕ → ℕ) (hc : GapCosts w 19) (k : ℕ)
    (hk : k + 3 < 19) (h0 : w k = 0) (h3 : w (k + 3) = 0)
    (ho : Occupied w k (k + 3)) : 2 ≤ intervalSum (excess w) (k + 1) (k + 3) := by
  have hm := hc.three k hk h0 h3 ho
  apply excess_of_mass w (k + 1) (k + 3) 2
  · intro i hi hir
    exact ho i (by omega) hir
  · omega

private theorem four_excess (w : ℕ → ℕ) (hc : GapCosts w 19) (k : ℕ)
    (hk : k + 4 < 19) (h0 : w k = 0) (h4 : w (k + 4) = 0)
    (ho : Occupied w k (k + 4)) : 1 ≤ intervalSum (excess w) (k + 1) (k + 4) := by
  have hm := hc.four k hk h0 h4 ho
  apply excess_of_mass w (k + 1) (k + 4) 1
  · intro i hi hir
    exact ho i (by omega) hir
  · omega

/-- Forward longer-gap baseline, using the first four interior sites for d≥5. -/
theorem forward_long {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b)
    (l r : ℕ) (hlr : l + 3 ≤ r) (hr : r < 19)
    (h0 : weight a b l = 0) (hR : weight a b r = 0)
    (ho : Occupied (weight a b) l r) :
    1 ≤ intervalSum (excess (weight a b)) (l + 1) r := by
  by_cases h3 : r = l + 3
  · subst r
    have hc := three_excess (weight a b) (forward_gapCosts hf ha) l hr h0 hR ho
    omega
  by_cases h4 : r = l + 4
  · subst r
    exact four_excess (weight a b) (forward_gapCosts hf ha) l hr h0 hR ho
  have h5 : l + 5 ≤ r := by omega
  have hm := forward_five hf l (by omega) h0
    (fun i hi hir => ho i hi (by omega))
  have hx : 1 ≤ intervalSum (excess (weight a b)) (l + 1) (l + 5) := by
    apply excess_of_mass (weight a b) (l + 1) (l + 5) 1
    · intro i hi hir
      exact ho i (by omega) (by omega)
    · omega
  exact hx.trans (intervalSum_mono _ (by omega) h5)

/-- Backward longer-gap baseline, using the final four interior sites for d≥5. -/
theorem backward_long {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b)
    (l r : ℕ) (hlr : l + 3 ≤ r) (hr : r < 19)
    (h0 : weight a b l = 0) (hR : weight a b r = 0)
    (ho : Occupied (weight a b) l r) :
    1 ≤ intervalSum (excess (weight a b)) (l + 1) r := by
  by_cases h3 : r = l + 3
  · subst r
    have hc := three_excess (weight a b) (backward_gapCosts hf ha) l hr h0 hR ho
    omega
  by_cases h4 : r = l + 4
  · subst r
    exact four_excess (weight a b) (backward_gapCosts hf ha) l hr h0 hR ho
  have h5 : l + 5 ≤ r := by omega
  have he : r - 5 + 5 = r := by omega
  have hm := backward_five hf (r - 5) (by omega)
    (by simpa only [he] using hR)
    (fun i hi hir => ho i (by omega) (by omega))
  rw [he] at hm
  have hx : 1 ≤ intervalSum (excess (weight a b)) (r - 5 + 1) r := by
    apply excess_of_mass (weight a b) (r - 5 + 1) r 1
    · intro i hi hir
      exact ho i (by omega) hir
    · omega
  exact hx.trans (intervalSum_mono _ (by omega) (by omega))

/-- Incoming F short gap: its middle is A-only and nonzero. The three actual
exit equations imply the two-unit gap / three-unit middle alternative. -/
theorem forward_incoming {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b)
    (l r : ℕ) (hl : 2 ≤ l) (hlr : l + 3 ≤ r) (hr : r < 19)
    (hprev : weight a b (l - 2) = 0) (h0 : weight a b l = 0)
    (hR : weight a b r = 0) (ho : Occupied (weight a b) l r) :
    2 ≤ intervalSum (excess (weight a b)) (l + 1) r ∨ 3 ≤ weight a b (l - 1) := by
  by_cases h3 : r = l + 3
  · subst r
    exact Or.inl (three_excess (weight a b) (forward_gapCosts hf ha) l hr h0 hR ho)
  have h4 : l + 4 ≤ r := by omega
  obtain ⟨hap, hbp⟩ := zero_blocks hprev
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  have ek := hf l hl (by omega)
  simp only [hap, hbp, ha0, hb0, mul_zero, zero_add, add_zero] at ek
  have hbmid : b (l - 1) = 0 := ek.symm
  have hocc := ha (l - 1) (by omega)
  rw [show l - 1 + 1 = l by omega, h0, add_zero] at hocc
  have hp : a (l - 1) ≠ 0 := by
    intro hz
    simp [weight, pairWt, hz, hbmid] at hocc
  have e0 := hf (l + 1) (by omega) (by omega)
  rw [show l + 1 - 2 = l - 1 by omega, show l + 1 - 1 = l by omega] at e0
  have e1 := forward_step hf l (by omega)
  have e2 := forward_step hf (l + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, hbmid,
    mul_zero, zero_add, add_zero] at e0 e1 e2
  have halt := exit_alternative_forward (a (l - 1))
    (a (l + 1)) (b (l + 1)) (a (l + 2)) (b (l + 2)) (a (l + 3)) (b (l + 3)) hp
    (ho (l + 2) (by omega) (by omega)) (ho (l + 3) (by omega) (by omega))
    (by linear_combination (norm := (ring_nf <;> simp)) e0)
    (by linear_combination (norm := (ring_nf <;> simp)) e1)
    (by linear_combination (norm := (ring_nf <;> simp)) e2)
  rcases halt with hx | hpw
  · left
    have he : intervalSum (excess (weight a b)) (l + 1) (l + 4) =
        exitExcess (a (l + 1)) (b (l + 1)) (a (l + 2)) (b (l + 2))
          (a (l + 3)) (b (l + 3)) := by
      simpa [excess, weight, exitExcess, Nat.add_assoc] using
        three_sum (excess (weight a b)) (l + 1)
    rw [← he] at hx
    exact hx.trans (intervalSum_mono _ (by omega) h4)
  · right
    simpa [weight, pairWt, hbmid] using hpw

/-- Incoming B short gap: its middle is B-only. All local equations are taken
from B directly; only the order of the three excess summands is reversed. -/
theorem backward_incoming {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b)
    (l r : ℕ) (hr : r + 2 < 19) (hlr : l + 3 ≤ r)
    (hnext : weight a b (r + 2) = 0) (h0 : weight a b l = 0)
    (hR : weight a b r = 0) (ho : Occupied (weight a b) l r) :
    2 ≤ intervalSum (excess (weight a b)) (l + 1) r ∨ 3 ≤ weight a b (r + 1) := by
  by_cases h3 : r = l + 3
  · subst r
    exact Or.inl (three_excess (weight a b) (backward_gapCosts hf ha) l (by omega) h0 hR ho)
  have h4 : l + 4 ≤ r := by omega
  obtain ⟨han, hbn⟩ := zero_blocks hnext
  obtain ⟨haR, hbR⟩ := zero_blocks hR
  have ek := backward_step hf r (by omega)
  simp only [han, hbn, haR, hbR, mul_zero, zero_add, add_zero] at ek
  have hamid : a (r + 1) = 0 := s_mul_eq_zero.mp ek.symm
  have hocc := ha r (by omega)
  rw [hR, zero_add] at hocc
  have hp : b (r + 1) ≠ 0 := by
    intro hz
    simp [weight, pairWt, hz, hamid] at hocc
  have e0 := hf (r + 1) (by omega) (by omega)
  rw [show r + 1 - 1 = r by omega, show r + 1 - 2 = r - 1 by omega] at e0
  have e1 := hf r (by omega) (by omega)
  have e2 := hf (r - 1) (by omega) (by omega)
  rw [show r - 1 - 1 = r - 2 by omega, show r - 1 - 2 = r - 3 by omega] at e2
  simp only [hamid, haR, hbR, mul_zero, zero_add, add_zero] at e0 e1 e2
  have halt := exit_alternative_backward (b (r + 1))
    (a (r - 1)) (b (r - 1)) (a (r - 2)) (b (r - 2)) (a (r - 3)) (b (r - 3)) hp
    (ho (r - 2) (by omega) (by omega)) (ho (r - 3) (by omega) (by omega))
    e0.symm
    (by linear_combination (norm := (ring_nf <;> simp)) e1)
    (by linear_combination (norm := (ring_nf <;> simp)) e2)
  rcases halt with hx | hpw
  · left
    have he : intervalSum (excess (weight a b)) (r - 3) r =
        exitExcess (a (r - 1)) (b (r - 1)) (a (r - 2)) (b (r - 2))
          (a (r - 3)) (b (r - 3)) := by
      have he := three_sum (excess (weight a b)) (r - 3)
      rw [show r - 3 + 3 = r by omega, show r - 3 + 1 = r - 2 by omega,
        show r - 3 + 2 = r - 1 by omega] at he
      simpa [excess, weight, exitExcess, add_comm, add_left_comm, add_assoc] using he
    rw [← he] at hx
    exact hx.trans (intervalSum_mono _ (by omega) (by omega))
  · right
    simpa [weight, pairWt, hamid] using hpw

/-- Every forward run-counting hypothesis follows from the actual arrays. -/
theorem forward_costs {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    ForwardCosts (weight a b) where
  adjacent i hi := ha i (by omega)
  branch := forward_branch hf ha
  long := forward_long hf ha
  incoming := forward_incoming hf ha

/-- Every backward run-counting hypothesis follows from the actual arrays. -/
theorem backward_costs {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    BackwardCosts (weight a b) where
  adjacent i hi := ha i (by omega)
  branch := backward_branch hf ha
  long := backward_long hf ha
  incoming := backward_incoming hf ha

/-- The polynomial strip theorem, F, without any degree restriction. -/
theorem forward_weight_ge_seventeen (a b : ℕ → P) (hf : Forward a b) (ha : Adjacent a b) :
    17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripRunCounting.weight_ge_seventeen_forward (weight a b) (forward_costs hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- The polynomial strip theorem, B, from its separate local algebra. -/
theorem backward_weight_ge_seventeen (a b : ℕ → P) (hf : Backward a b) (ha : Adjacent a b) :
    17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripRunCounting.weight_ge_seventeen_backward (weight a b) (backward_costs hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- Eighteen holds in F unless the final short gap has no on-board exit. -/
theorem forward_weight_ge_eighteen (a b : ℕ → P) (hf : Forward a b) (ha : Adjacent a b)
    (hexit : ¬ (weight a b 16 = 0 ∧ weight a b 18 = 0)) :
    18 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripRunCounting.weight_ge_eighteen_forward (weight a b) (forward_costs hf ha) hexit
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- Eighteen holds in B unless its final short gap has no on-board exit. -/
theorem backward_weight_ge_eighteen (a b : ℕ → P) (hf : Backward a b) (ha : Adjacent a b)
    (hexit : ¬ (weight a b 0 = 0 ∧ weight a b 2 = 0)) :
    18 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripRunCounting.weight_ge_eighteen_backward (weight a b) (backward_costs hf ha) hexit
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- Either exact recurrence suffices for the seventeen bound. -/
theorem weight_ge_seventeen (a b : ℕ → P) (hf : Forward a b ∨ Backward a b)
    (ha : Adjacent a b) : 17 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  rcases hf with hf | hf
  · exact forward_weight_ge_seventeen a b hf ha
  · exact backward_weight_ge_seventeen a b hf ha

end
end QldpcVerification.Planar.StripRunRecurrence
