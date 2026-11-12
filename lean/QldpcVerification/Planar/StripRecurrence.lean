import QldpcVerification.Planar.StripFamilyRecurrence

/-!
# Nineteen-slice compatibility interface

The definitions retain their original normal forms. All local recurrence,
gap, and branch proofs specialize the family theory at `N = 16`.
The historical fifteen bound is retained through the original counting
interface, now supplied entirely by those family specializations.
-/

namespace QldpcVerification.Planar.StripRecurrence

open StripLocal StripCounting
open scoped CharTwo

noncomputable section

/-- Actual physical block weight at one array index. -/
def weight (a b : ℕ → P) (i : ℕ) : ℕ := pairWt (a i) (b i)

/-- Forward recurrence, only at indices 2 through 18. -/
def Forward (a b : ℕ → P) : Prop :=
  ∀ i, 2 ≤ i → i ≤ 18 →
    a i = t * a (i - 2) + b (i - 1) + b (i - 2) + s * b i

/-- Backward recurrence, only at indices 2 through 18. -/
def Backward (a b : ℕ → P) : Prop :=
  ∀ i, 2 ≤ i → i ≤ 18 →
    t * b i = a i + s * a (i - 1) + s * a (i - 2) + b (i - 2)

/-- No two adjacent slices of the nineteen-slice strip are empty. -/
def Adjacent (a b : ℕ → P) : Prop :=
  ∀ i, i ≤ 17 → 1 ≤ weight a b i + weight a b (i + 1)

theorem zero_blocks {a b : ℕ → P} {i : ℕ} (h : weight a b i = 0) :
    a i = 0 ∧ b i = 0 := by
  exact StripFamilyRecurrence.zero_blocks h

theorem forward_step {a b : ℕ → P} (hf : Forward a b) (k : ℕ) (hk : k ≤ 16) :
    a (k + 2) = t * a k + b (k + 1) + b k + s * b (k + 2) := by
  exact StripFamilyRecurrence.forward_step (N := 16) hf k hk

theorem backward_step {a b : ℕ → P} (hf : Backward a b) (k : ℕ) (hk : k ≤ 16) :
    t * b (k + 2) = a (k + 2) + s * a (k + 1) + s * a k + b k := by
  exact StripFamilyRecurrence.backward_step (N := 16) hf k hk

theorem forward_three {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 3 < 19) (h0 : weight a b k = 0) (h3 : weight a b (k + 3) = 0)
    (ho : Occupied (weight a b) k (k + 3)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 3) := by
  exact StripFamilyRecurrence.forward_three (N := 16) hf k hk h0 h3 ho

theorem backward_three {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 3 < 19) (h0 : weight a b k = 0) (h3 : weight a b (k + 3) = 0)
    (ho : Occupied (weight a b) k (k + 3)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 3) := by
  exact StripFamilyRecurrence.backward_three (N := 16) hf k hk h0 h3 ho

theorem forward_four {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 4 < 19) (h0 : weight a b k = 0) (h4 : weight a b (k + 4) = 0)
    (ho : Occupied (weight a b) k (k + 4)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 4) := by
  exact StripFamilyRecurrence.forward_four (N := 16) hf k hk h0 h4 ho

theorem backward_four {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 4 < 19) (h0 : weight a b k = 0) (h4 : weight a b (k + 4) = 0)
    (ho : Occupied (weight a b) k (k + 4)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 4) := by
  exact StripFamilyRecurrence.backward_four (N := 16) hf k hk h0 h4 ho

theorem forward_five {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 5 < 19) (h0 : weight a b k = 0)
    (ho : Occupied (weight a b) k (k + 5)) :
    5 ≤ intervalSum (weight a b) (k + 1) (k + 5) := by
  exact StripFamilyRecurrence.forward_five (N := 16) hf k hk h0 ho

theorem backward_five {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 5 < 19) (h5 : weight a b (k + 5) = 0)
    (ho : Occupied (weight a b) k (k + 5)) :
    5 ≤ intervalSum (weight a b) (k + 1) (k + 5) := by
  exact StripFamilyRecurrence.backward_five (N := 16) hf k hk h5 ho

theorem forward_gapCosts {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    GapCosts (weight a b) 19 := by
  exact StripFamilyRecurrence.forward_gapCosts (N := 16) hf ha

theorem backward_gapCosts {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    GapCosts (weight a b) 19 := by
  exact StripFamilyRecurrence.backward_gapCosts (N := 16) hf ha

theorem forward_branch {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    ForwardBranch (weight a b) 19 := by
  exact StripFamilyRecurrence.forward_branch (N := 16) hf ha

theorem backward_branch {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    BackwardBranch (weight a b) 19 := by
  exact StripFamilyRecurrence.backward_branch (N := 16) hf ha

theorem forward_weight_ge_fifteen (a b : ℕ → P) (hf : Forward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripCounting.weight_ge_fifteen_forward (weight a b)
    (forward_gapCosts hf ha) (forward_branch hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

theorem backward_weight_ge_fifteen (a b : ℕ → P) (hf : Backward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripCounting.weight_ge_fifteen_backward (weight a b)
    (backward_gapCosts hf ha) (backward_branch hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

theorem weight_ge_fifteen (a b : ℕ → P) (hf : Forward a b ∨ Backward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  rcases hf with hf | hf
  · exact forward_weight_ge_fifteen a b hf ha
  · exact backward_weight_ge_fifteen a b hf ha

end
end QldpcVerification.Planar.StripRecurrence
