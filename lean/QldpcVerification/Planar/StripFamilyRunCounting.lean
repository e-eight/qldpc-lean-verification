import QldpcVerification.Planar.StripCounting

/-! Polynomial strip estimates for arbitrary length `N + 3`.
The local algebra is shared with StripLocal and StripRunLocal; all global
indices and endpoint accounting are symbolic. -/

namespace QldpcVerification.Planar.StripFamilyRunCounting

open Finset StripCounting

variable {N : ℕ}

/-- Exactly the forward missing-exit configuration, not an arbitrary slack. -/
def missingForward (N : ℕ) (w : ℕ → ℕ) : ℕ := if w N = 0 ∧ w (N + 2) = 0 then 1 else 0

def missingBackward (w : ℕ → ℕ) : ℕ := if w 0 = 0 ∧ w 2 = 0 then 1 else 0

/-- Local forward hypotheses. `incoming` concerns a long gap preceded by a
short gap, and gives precisely the extra-unit/terminal-feed alternative. -/
structure ForwardCosts (N : ℕ) (w : ℕ → ℕ) : Prop where
  adjacent : ∀ i, i + 1 < (N + 3) → 1 ≤ w i + w (i + 1)
  branch : ForwardBranch w (N + 3)
  long : ∀ a b, a + 3 ≤ b → b < (N + 3) → w a = 0 → w b = 0 → Occupied w a b →
    1 ≤ intervalSum (excess w) (a + 1) b
  incoming : ∀ a b, 2 ≤ a → a + 3 ≤ b → b < (N + 3) →
    w (a - 2) = 0 → w a = 0 → w b = 0 → Occupied w a b →
    2 ≤ intervalSum (excess w) (a + 1) b ∨ 3 ≤ w (a - 1)

/-- Backward local hypotheses in the original, increasing index convention.
The incoming short gap is on the right; its terminal middle is `b+1`. -/
structure BackwardCosts (N : ℕ) (w : ℕ → ℕ) : Prop where
  adjacent : ∀ i, i + 1 < (N + 3) → 1 ≤ w i + w (i + 1)
  branch : BackwardBranch w (N + 3)
  long : ∀ a b, a + 3 ≤ b → b < (N + 3) → w a = 0 → w b = 0 → Occupied w a b →
    1 ≤ intervalSum (excess w) (a + 1) b
  incoming : ∀ a b, b + 2 < (N + 3) → a + 3 ≤ b →
    w (b + 2) = 0 → w a = 0 → w b = 0 → Occupied w a b →
    2 ≤ intervalSum (excess w) (a + 1) b ∨ 3 ≤ w (b + 1)

theorem missingForward_le_one (w : ℕ → ℕ) : missingForward N w ≤ 1 := by
  unfold missingForward
  split_ifs <;> omega

/-- The half-open short gap contains just its zero endpoint and its middle. -/
theorem short_excess (w : ℕ → ℕ) (a : ℕ) (ha : w a = 0) :
    intervalSum (excess w) a (a + 2) = w (a + 1) - 1 := by
  rw [intervalSum_head _ (by omega : a < a + 2),
    intervalSum_head _ (by omega : a + 1 < a + 2)]
  simp [intervalSum, excess, ha, Nat.add_assoc]

/-- Simultaneous ordinary and incoming-run budgets for a suffix beginning
at an actual zero. The incoming state leaves the already-reserved baseline
unit at the previous middle untouched. -/
theorem zero_suffix_budget (w : ℕ → ℕ) (costs : ForwardCosts N w)
    (a : ℕ) (ha : a < (N + 3)) (ha0 : w a = 0) :
    (intervalSum (zeroIndicator w) a (N + 3) ≤ intervalSum (excess w) a (N + 3) +
      1 + missingForward N w) ∧
    (2 ≤ a → w (a - 2) = 0 →
      intervalSum (zeroIndicator w) a (N + 3) ≤ intervalSum (excess w) a (N + 3) +
        missingForward N w + (w (a - 1) - 2)) := by
  classical
  suffices ∀ d a, (N + 3) - a = d → a < (N + 3) → w a = 0 →
      (intervalSum (zeroIndicator w) a (N + 3) ≤ intervalSum (excess w) a (N + 3) +
        1 + missingForward N w) ∧
      (2 ≤ a → w (a - 2) = 0 →
        intervalSum (zeroIndicator w) a (N + 3) ≤ intervalSum (excess w) a (N + 3) +
          missingForward N w + (w (a - 1) - 2)) from this ((N + 3) - a) a rfl ha ha0
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hda ha ha0
    by_cases hnxt : ∃ b, a < b ∧ b < (N + 3) ∧ w b = 0
    · let b := Nat.find hnxt
      have hb := Nat.find_spec hnxt
      change a < b ∧ b < (N + 3) ∧ w b = 0 at hb
      have hocc : Occupied w a b := by
        intro i hai hib
        by_contra hi
        have hi0 : w i = 0 := by omega
        have hmin : b ≤ i := Nat.find_min' hnxt ⟨hai, by omega, hi0⟩
        omega
      have hsep : a + 2 ≤ b := by
        by_contra hh
        have heq : b = a + 1 := by omega
        have hadj := costs.adjacent a (by omega)
        rw [← heq, ha0, hb.2.2] at hadj
        omega
      obtain ⟨htail, hincoming⟩ := ih ((N + 3) - b) (by omega) b rfl hb.2.1 hb.2.2
      have hz : intervalSum (zeroIndicator w) a (N + 3) =
          1 + intervalSum (zeroIndicator w) b (N + 3) := by
        rw [intervalSum_split _ (by omega : a ≤ b) (by omega : b ≤ (N + 3)),
          gap_zero_count w hb.1 ha0 hocc]
      have he := intervalSum_split (excess w) (by omega : a ≤ b) (by omega : b ≤ (N + 3))
      by_cases hshort : b = a + 2
      · have hm₂ : b - 2 = a := by omega
        have hm₁ : b - 1 = a + 1 := by omega
        have ht : intervalSum (zeroIndicator w) b (N + 3) ≤ intervalSum (excess w) b (N + 3) +
            missingForward N w + (w (a + 1) - 2) := by
          simpa only [hm₂, hm₁] using hincoming (by omega) (by simpa only [hm₂] using ha0)
        have hhead : intervalSum (excess w) a b = w (a + 1) - 1 := by
          rw [hshort]
          exact short_excess w a ha0
        constructor
        · omega
        · intro ha₂ hprev
          have hm : a - 2 + 2 = a := by omega
          have htgt : a - 2 + 3 = a + 1 := by omega
          have hheavy : 2 ≤ w (a + 1) := by
            simpa only [htgt] using costs.branch (a - 2) (by omega) hprev
              (by simpa only [hm] using ha0)
          omega
      · have hlong := costs.long a b (by omega) hb.2.1 ha0 hb.2.2 hocc
        have hhead : intervalSum (excess w) a b = intervalSum (excess w) (a + 1) b := by
          rw [intervalSum_head _ hb.1]
          simp [excess, ha0]
        constructor
        · omega
        · intro ha₂ hprev
          have halt := costs.incoming a b ha₂ (by omega) hb.2.1 hprev ha0 hb.2.2 hocc
          rcases halt with hgap | hfeed <;> omega
    · have hocc : Occupied w a (N + 3) := by
        intro i hai hi19
        by_contra hi
        exact hnxt ⟨i, hai, hi19, by omega⟩
      have hz := gap_zero_count w ha ha0 hocc
      constructor
      · omega
      · intro ha₂ hprev
        by_cases hexit : a + 1 < (N + 3)
        · have hm : a - 2 + 2 = a := by omega
          have htgt : a - 2 + 3 = a + 1 := by omega
          have hheavy : 2 ≤ w (a + 1) := by
            simpa only [htgt] using costs.branch (a - 2) (by omega) hprev
              (by simpa only [hm] using ha0)
          have hu : 1 ≤ excess w (a + 1) := by dsimp [excess]; omega
          have he₀ := intervalSum_head (excess w) ha
          have he₁ := intervalSum_head (excess w) hexit
          omega
        · have heq : a = (N + 2) := by omega
          subst a
          have h16 : w N = 0 := by simpa using hprev
          have heps : missingForward N w = 1 := by simp [missingForward, h16, ha0]
          omega

/-- Construct the first zero and all successive gaps of the actual sequence.
This is the draft's `E ≥ z-1-ε`, written without truncated subtraction. -/
theorem forward_excess_budget (w : ℕ → ℕ) (costs : ForwardCosts N w) :
    intervalSum (zeroIndicator w) 0 (N + 3) ≤ intervalSum (excess w) 0 (N + 3) +
      1 + missingForward N w := by
  classical
  by_cases hz : ∃ a, a < (N + 3) ∧ w a = 0
  · let a := Nat.find hz
    have ha := Nat.find_spec hz
    change a < (N + 3) ∧ w a = 0 at ha
    have hpref : intervalSum (zeroIndicator w) 0 a = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := mem_Ico.mp hi
      have hne : w i ≠ 0 := by
        intro hi0
        have hmin : a ≤ i := Nat.find_min' hz ⟨by omega, hi0⟩
        omega
      simp [zeroIndicator, hne]
    have hsuf := (zero_suffix_budget w costs a ha.1 ha.2).1
    have he := intervalSum_mono (excess w) (a := 0) (b := (N + 3))
      (c := a) (d := (N + 3)) (by omega) (by omega)
    rw [intervalSum_split _ (by omega : 0 ≤ a) (by omega : a ≤ (N + 3)), hpref]
    omega
  · have hnone : intervalSum (zeroIndicator w) 0 (N + 3) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := mem_Ico.mp hi
      have hne : w i ≠ 0 := fun hi0 => hz ⟨i, hi'.2, hi0⟩
      simp [zeroIndicator, hne]
    rw [hnone]
    omega

/-- Endpoint-sensitive bound: eighteen minus exactly the missing-exit bit. -/
theorem forward_weight_with_endpoint (w : ℕ → ℕ) (costs : ForwardCosts N w) :
    (N + 2) ≤ intervalSum w 0 (N + 3) + missingForward N w := by
  have he := forward_excess_budget w costs
  have hm := mass_identity w 0 (N + 3)
  omega

theorem weight_ge_length_sub_two_forward (w : ℕ → ℕ) (costs : ForwardCosts N w) :
    (N + 1) ≤ intervalSum w 0 (N + 3) := by
  have hw := forward_weight_with_endpoint w costs
  have he := missingForward_le_one (N := N) w
  omega

theorem weight_ge_length_sub_one_forward (w : ℕ → ℕ) (costs : ForwardCosts N w)
    (hexit : ¬ (w N = 0 ∧ w (N + 2) = 0)) : (N + 2) ≤ intervalSum w 0 (N + 3) := by
  have hw := forward_weight_with_endpoint w costs
  simpa [missingForward, hexit] using hw

/-- Reverse only the nineteen indices used by the counting argument. Values
outside that interval are immaterial to every hypothesis and conclusion. -/
def reverseWeights (N : ℕ) (w : ℕ → ℕ) (i : ℕ) : ℕ := w ((N + 2) - i)

/-- Reflection is a bijection of these actual interval indices. -/
theorem reverse_interval (f : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ (N + 3)) :
    intervalSum (reverseWeights N f) a b = intervalSum f ((N + 3) - b) ((N + 3) - a) := by
  unfold intervalSum reverseWeights
  apply Finset.sum_bij (fun i _ => (N + 2) - i)
  · intro i hi
    simp only [mem_Ico] at hi ⊢
    omega
  · intro i hi j hj hij
    simp only [mem_Ico] at hi hj
    omega
  · intro j hj
    have hj' := mem_Ico.mp hj
    refine ⟨(N + 2) - j, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro i hi
    rfl

theorem reverse_total (w : ℕ → ℕ) :
    intervalSum (reverseWeights N w) 0 (N + 3) = intervalSum w 0 (N + 3) := by
  simpa only [Nat.sub_self, Nat.sub_zero] using
    reverse_interval (N := N) w (a := 0) (b := (N + 3)) (by omega) (by omega)

theorem reverse_excess_total (w : ℕ → ℕ) :
    intervalSum (excess (reverseWeights N w)) 0 (N + 3) = intervalSum (excess w) 0 (N + 3) :=
  reverse_total (excess w)

theorem reverse_zero_total (w : ℕ → ℕ) :
    intervalSum (zeroIndicator (reverseWeights N w)) 0 (N + 3) =
      intervalSum (zeroIndicator w) 0 (N + 3) := reverse_total (zeroIndicator w)

theorem missingForward_reverse (w : ℕ → ℕ) :
    missingForward N (reverseWeights N w) = missingBackward w := by
  simp [missingForward, missingBackward, reverseWeights, and_comm]

/-- Reflection transports the *entire* occupied gap, not just its endpoints. -/
theorem reverse_occupied (w : ℕ → ℕ) {a b : ℕ} (hab : a < b) (hb : b < (N + 3))
    (hocc : Occupied (reverseWeights N w) a b) : Occupied w ((N + 2) - b) ((N + 2) - a) := by
  intro i hi₀ hi₁
  have heq : (N + 2) - ((N + 2) - i) = i := by omega
  have hp := hocc ((N + 2) - i) (by omega) (by omega)
  simpa only [reverseWeights, heq] using hp

theorem reverse_gap_excess (w : ℕ → ℕ) {a b : ℕ} (hab : a < b) (hb : b < (N + 3)) :
    intervalSum (excess (reverseWeights N w)) (a + 1) b =
      intervalSum (excess w) ((N + 2) - b + 1) ((N + 2) - a) := by
  change intervalSum (reverseWeights N (excess w)) (a + 1) b = _
  rw [reverse_interval (excess w) (by omega : a + 1 ≤ b) (by omega : b ≤ (N + 3))]
  have h₀ : (N + 3) - b = (N + 2) - b + 1 := by omega
  have h₁ : (N + 3) - (a + 1) = (N + 2) - a := by omega
  rw [h₀, h₁]

/-- All backward local hypotheses become the forward local hypotheses under
the proved index reflection; this does not assert a polynomial/code symmetry. -/
theorem backwardCosts_reverse (w : ℕ → ℕ) (costs : BackwardCosts N w) :
    ForwardCosts N (reverseWeights N w) := by
  constructor
  · intro i hi
    have h := costs.adjacent ((N + 1) - i) (by omega)
    have h₀ : (N + 1) - i + 1 = (N + 2) - i := by omega
    have h₁ : (N + 2) - (i + 1) = (N + 1) - i := by omega
    rw [h₀] at h
    change 1 ≤ w ((N + 2) - i) + w ((N + 2) - (i + 1))
    rw [h₁]
    omega
  · intro a ha ha0 ha2
    have h₀ : (N + 2) - (a + 2) + 2 = (N + 2) - a := by omega
    have h₁ : (N + 2) - (a + 2) - 1 = (N + 2) - (a + 3) := by omega
    have ht := costs.branch ((N + 2) - (a + 2)) (by omega) (by omega) ha2
      (by simpa only [h₀] using ha0)
    change 2 ≤ w ((N + 2) - (a + 3))
    simpa only [h₁] using ht
  · intro a b hlong hb ha0 hb0 hocc
    rw [reverse_gap_excess w (by omega : a < b) hb]
    exact costs.long ((N + 2) - b) ((N + 2) - a) (by omega) (by omega) hb0 ha0
      (reverse_occupied w (by omega) hb hocc)
  · intro a b ha hlong hb hprev ha0 hb0 hocc
    have h₀ : (N + 2) - a + 2 = (N + 2) - (a - 2) := by omega
    have h₁ : (N + 2) - a + 1 = (N + 2) - (a - 1) := by omega
    have ht := costs.incoming ((N + 2) - b) ((N + 2) - a) (by omega) (by omega)
      (by simpa only [h₀] using hprev) hb0 ha0
      (reverse_occupied w (by omega) hb hocc)
    rcases ht with hgap | hfeed
    · left
      rw [reverse_gap_excess w (by omega : a < b) hb]
      exact hgap
    · right
      change 3 ≤ w ((N + 2) - (a - 1))
      simpa only [h₁] using hfeed

theorem backward_excess_budget (w : ℕ → ℕ) (costs : BackwardCosts N w) :
    intervalSum (zeroIndicator w) 0 (N + 3) ≤ intervalSum (excess w) 0 (N + 3) +
      1 + missingBackward w := by
  have h := forward_excess_budget (reverseWeights N w) (backwardCosts_reverse w costs)
  simpa only [reverse_zero_total, reverse_excess_total, missingForward_reverse] using h

theorem backward_weight_with_endpoint (w : ℕ → ℕ) (costs : BackwardCosts N w) :
    (N + 2) ≤ intervalSum w 0 (N + 3) + missingBackward w := by
  have h := forward_weight_with_endpoint (reverseWeights N w) (backwardCosts_reverse w costs)
  simpa only [reverse_total, missingForward_reverse] using h

theorem weight_ge_length_sub_two_backward (w : ℕ → ℕ) (costs : BackwardCosts N w) :
    (N + 1) ≤ intervalSum w 0 (N + 3) := by
  have h := weight_ge_length_sub_two_forward (reverseWeights N w) (backwardCosts_reverse w costs)
  simpa only [reverse_total] using h

theorem weight_ge_length_sub_one_backward (w : ℕ → ℕ) (costs : BackwardCosts N w)
    (hexit : ¬ (w 0 = 0 ∧ w 2 = 0)) : (N + 2) ≤ intervalSum w 0 (N + 3) := by
  have hw := backward_weight_with_endpoint w costs
  simpa [missingBackward, hexit] using hw

end QldpcVerification.Planar.StripFamilyRunCounting
