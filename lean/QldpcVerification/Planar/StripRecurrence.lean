import QldpcVerification.Planar.StripLocal
import QldpcVerification.Planar.StripCounting

/-!
# Polynomial strip recurrences imply weight at least fifteen

The frozen strip draft's F/B systems on indices 0,...,18, using ordinary
polynomials over ZMod 2. `t = X + X²`, `s = X²`; neither products nor exponents
are truncated. No degree bound or physical-model hypothesis is needed.

The adapters below derive every gap cost and directional branch from the
actual recurrence equations. The counting module supplies the decomposition,
charging multiplicities, endpoint exceptions, and integer rounding.
Author design checks only: F/B equations, index ranges, and order of B's
four-slice arguments. No independent source review or local Lean run claimed.
Validation is delegated to the main agent's detached capped runner.
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
  change wt (a i) + wt (b i) = 0 at h
  exact ⟨wt_eq_zero.mp (by omega), wt_eq_zero.mp (by omega)⟩

theorem forward_step {a b : ℕ → P} (hf : Forward a b) (k : ℕ) (hk : k ≤ 16) :
    a (k + 2) = t * a k + b (k + 1) + b k + s * b (k + 2) := by
  have h1 : k + 2 - 1 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  simpa only [h1, h2] using hf (k + 2) (by omega) (by omega)

theorem backward_step {a b : ℕ → P} (hf : Backward a b) (k : ℕ) (hk : k ≤ 16) :
    t * b (k + 2) = a (k + 2) + s * a (k + 1) + s * a k + b k := by
  have h1 : k + 2 - 1 = k + 1 := by omega
  have h2 : k + 2 - 2 = k := by omega
  simpa only [h1, h2] using hf (k + 2) (by omega) (by omega)

private theorem sum_two (w : ℕ → ℕ) (k : ℕ) :
    intervalSum w (k + 1) (k + 3) = w (k + 1) + w (k + 2) := by
  unfold intervalSum
  rw [Finset.sum_Ico_eq_sum_range, show k + 3 - (k + 1) = 2 by omega]
  simp [Finset.sum_range_succ, Nat.add_assoc]

private theorem sum_three (w : ℕ → ℕ) (k : ℕ) :
    intervalSum w (k + 1) (k + 4) = w (k + 1) + w (k + 2) + w (k + 3) := by
  unfold intervalSum
  rw [Finset.sum_Ico_eq_sum_range, show k + 4 - (k + 1) = 3 by omega]
  simp [Finset.sum_range_succ, Nat.add_assoc]

private theorem sum_four (w : ℕ → ℕ) (k : ℕ) :
    intervalSum w (k + 1) (k + 5) =
      w (k + 1) + w (k + 2) + w (k + 3) + w (k + 4) := by
  unfold intervalSum
  rw [Finset.sum_Ico_eq_sum_range, show k + 5 - (k + 1) = 4 by omega]
  simp [Finset.sum_range_succ, Nat.add_assoc]

/-- The length-three F gap costs four, derived from equations k+2,k+3. -/
theorem forward_three {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 3 < 19) (h0 : weight a b k = 0) (h3 : weight a b (k + 3) = 0)
    (ho : Occupied (weight a b) k (k + 3)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 3) := by
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha3, hb3⟩ := zero_blocks h3
  have e2 := forward_step hf k (by omega)
  have e3 := forward_step hf (k + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha3, hb3,
    mul_zero, zero_add, add_zero] at e2 e3
  have hocc := ho (k + 1) (by omega) (by omega)
  rw [sum_two]
  exact gap_three_forward (a (k + 1)) (b (k + 1)) (a (k + 2)) (b (k + 2))
    e2 (by simpa [add_comm, add_left_comm, add_assoc] using e3.symm)
    (by change 0 < pairWt _ _ at hocc; omega)

/-- The length-three B gap uses its own equations, not a reversal of F. -/
theorem backward_three {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 3 < 19) (h0 : weight a b k = 0) (h3 : weight a b (k + 3) = 0)
    (ho : Occupied (weight a b) k (k + 3)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 3) := by
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha3, hb3⟩ := zero_blocks h3
  have e2 := backward_step hf k (by omega)
  have e3 := backward_step hf (k + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha3, hb3,
    mul_zero, zero_add, add_zero] at e2 e3
  have hocc := ho (k + 1) (by omega) (by omega)
  rw [sum_two]
  apply gap_three_backward (a (k + 1)) (b (k + 1)) (a (k + 2)) (b (k + 2)) e2
  · linear_combination (norm := (ring_nf <;> simp)) e3
  · change 0 < pairWt _ _ at hocc
    omega

/-- F equations at k+2,k+3,k+4 give the length-four gap cost. -/
theorem forward_four {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 4 < 19) (h0 : weight a b k = 0) (h4 : weight a b (k + 4) = 0)
    (ho : Occupied (weight a b) k (k + 4)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 4) := by
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha4, hb4⟩ := zero_blocks h4
  have e2 := forward_step hf k (by omega)
  have e3 := forward_step hf (k + 1) (by omega)
  have e4 := forward_step hf (k + 2) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha4, hb4,
    mul_zero, zero_add, add_zero] at e2 e3 e4
  rw [sum_three]
  exact gap_four_forward (a (k + 1)) (b (k + 1)) (a (k + 2)) (b (k + 2))
    (a (k + 3)) (b (k + 3)) e2 e3 e4
    (ho (k + 1) (by omega) (by omega))
    (ho (k + 2) (by omega) (by omega))
    (ho (k + 3) (by omega) (by omega))

/-- B equations at k+2,k+3,k+4 give the length-four gap cost. -/
theorem backward_four {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 4 < 19) (h0 : weight a b k = 0) (h4 : weight a b (k + 4) = 0)
    (ho : Occupied (weight a b) k (k + 4)) :
    4 ≤ intervalSum (weight a b) (k + 1) (k + 4) := by
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha4, hb4⟩ := zero_blocks h4
  have e2 := backward_step hf k (by omega)
  have e3 := backward_step hf (k + 1) (by omega)
  have e4 := backward_step hf (k + 2) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha4, hb4,
    mul_zero, zero_add, add_zero] at e2 e3 e4
  rw [sum_three]
  apply gap_four_backward (a (k + 1)) (b (k + 1)) (a (k + 2)) (b (k + 2))
    (a (k + 3)) (b (k + 3)) e2 e3
  · linear_combination (norm := (ring_nf <;> simp)) e4
  · exact ho (k + 1) (by omega) (by omega)
  · exact ho (k + 2) (by omega) (by omega)
  · exact ho (k + 3) (by omega) (by omega)

/-- F needs only the left zero for the length-five gap cost. -/
theorem forward_five {a b : ℕ → P} (hf : Forward a b) (k : ℕ)
    (hk : k + 5 < 19) (h0 : weight a b k = 0)
    (ho : Occupied (weight a b) k (k + 5)) :
    5 ≤ intervalSum (weight a b) (k + 1) (k + 5) := by
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  have e2 := forward_step hf k (by omega)
  have e3 := forward_step hf (k + 1) (by omega)
  have e4 := forward_step hf (k + 2) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0,
    mul_zero, zero_add, add_zero] at e2 e3 e4
  rw [sum_four]
  apply gap_five_forward (a (k + 1)) (b (k + 1)) (a (k + 2)) (b (k + 2))
    (a (k + 3)) (b (k + 3)) (a (k + 4)) (b (k + 4))
  · linear_combination (norm := (ring_nf <;> simp)) e2
  · linear_combination (norm := (ring_nf <;> simp)) e3
  · linear_combination (norm := (ring_nf <;> simp)) e4
  · exact ho (k + 1) (by omega) (by omega)
  · exact ho (k + 2) (by omega) (by omega)
  · exact ho (k + 3) (by omega) (by omega)
  · exact ho (k + 4) (by omega) (by omega)

/-- B needs only the right zero; the local lemma takes slices in decreasing order. -/
theorem backward_five {a b : ℕ → P} (hf : Backward a b) (k : ℕ)
    (hk : k + 5 < 19) (h5 : weight a b (k + 5) = 0)
    (ho : Occupied (weight a b) k (k + 5)) :
    5 ≤ intervalSum (weight a b) (k + 1) (k + 5) := by
  obtain ⟨ha5, hb5⟩ := zero_blocks h5
  have e3 := backward_step hf (k + 1) (by omega)
  have e4 := backward_step hf (k + 2) (by omega)
  have e5 := backward_step hf (k + 3) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha5, hb5,
    mul_zero, zero_add, add_zero] at e3 e4 e5
  have hc := gap_five_backward (a (k + 4)) (b (k + 4)) (a (k + 3)) (b (k + 3))
    (a (k + 2)) (b (k + 2)) (a (k + 1)) (b (k + 1))
    (by linear_combination (norm := (ring_nf <;> simp)) e5)
    (by linear_combination (norm := (ring_nf <;> simp)) e4)
    (by linear_combination (norm := (ring_nf <;> simp)) e3)
    (ho (k + 4) (by omega) (by omega))
    (ho (k + 3) (by omega) (by omega))
    (ho (k + 2) (by omega) (by omega))
    (ho (k + 1) (by omega) (by omega))
  rw [sum_four]
  change 5 ≤ pairWt _ _ + pairWt _ _ + pairWt _ _ + pairWt _ _
  omega

/-- All counting gap hypotheses are consequences of the F equations. -/
theorem forward_gapCosts {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    GapCosts (weight a b) 19 where
  adjacent i hi := ha i (by omega)
  three k hk h0 h3 ho := forward_three hf k hk h0 h3 ho
  four k hk h0 h4 ho := forward_four hf k hk h0 h4 ho
  five k hk h0 _ ho := forward_five hf k hk h0 ho

/-- All counting gap hypotheses are consequences of the B equations. -/
theorem backward_gapCosts {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    GapCosts (weight a b) 19 where
  adjacent i hi := ha i (by omega)
  three k hk h0 h3 ho := backward_three hf k hk h0 h3 ho
  four k hk h0 h4 ho := backward_four hf k hk h0 h4 ho
  five k hk _ h5 ho := backward_five hf k hk h5 ho

/-- F branch target k+3 is charged only when its recurrence is available. -/
theorem forward_branch {a b : ℕ → P} (hf : Forward a b) (ha : Adjacent a b) :
    ForwardBranch (weight a b) 19 := by
  intro k hk h0 h2
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha2, hb2⟩ := zero_blocks h2
  have e2 := forward_step hf k (by omega)
  have e3 := forward_step hf (k + 1) (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha2, hb2,
    mul_zero, zero_add, add_zero] at e2 e3
  have hkill : b (k + 1) = 0 := e2.symm
  have hocc := ha k (by omega)
  rw [h0, zero_add] at hocc
  exact (branch_forward (a (k + 1)) (b (k + 1)) (a (k + 3)) (b (k + 3))
    hkill (by rw [hkill] at e3; linear_combination (norm := (ring_nf <;> simp)) e3)
    hocc).2

/-- B branch target k-1 is charged only for k≥1, so equation k+1 exists. -/
theorem backward_branch {a b : ℕ → P} (hf : Backward a b) (ha : Adjacent a b) :
    BackwardBranch (weight a b) 19 := by
  intro k hk hk2 h0 h2
  obtain ⟨ha0, hb0⟩ := zero_blocks h0
  obtain ⟨ha2, hb2⟩ := zero_blocks h2
  have e2 := backward_step hf k (by omega)
  simp only [Nat.add_assoc, Nat.reduceAdd, ha0, hb0, ha2, hb2,
    mul_zero, zero_add, add_zero] at e2
  have hkill : s * a (k + 1) = 0 := e2.symm
  have hap : a (k + 1) = 0 := s_mul_eq_zero.mp hkill
  have e1 := backward_step hf (k - 1) (by omega)
  rw [show k - 1 + 2 = k + 1 by omega, show k - 1 + 1 = k by omega] at e1
  simp only [hap, ha0, mul_zero, zero_add, add_zero] at e1
  have hocc := ha k (by omega)
  rw [h0, zero_add] at hocc
  exact (branch_backward (a (k + 1)) (b (k + 1)) (a (k - 1)) (b (k - 1))
    hkill e1.symm hocc).2

/-- The frozen strip draft, forward system, for arbitrary polynomial arrays. -/
theorem forward_weight_ge_fifteen (a b : ℕ → P) (hf : Forward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripCounting.weight_ge_fifteen_forward (weight a b)
    (forward_gapCosts hf ha) (forward_branch hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- The frozen strip draft, backward system, for arbitrary polynomial arrays. -/
theorem backward_weight_ge_fifteen (a b : ℕ → P) (hf : Backward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  have hc := StripCounting.weight_ge_fifteen_backward (weight a b)
    (backward_gapCosts hf ha) (backward_branch hf ha)
  simpa [intervalSum, weight, Nat.Ico_zero_eq_range] using hc

/-- Either displayed recurrence suffices, with no degree or physical hypotheses. -/
theorem weight_ge_fifteen (a b : ℕ → P) (hf : Forward a b ∨ Backward a b)
    (ha : Adjacent a b) : 15 ≤ ∑ i ∈ Finset.range 19, pairWt (a i) (b i) := by
  rcases hf with hf | hf
  · exact forward_weight_ge_fifteen a b hf ha
  · exact backward_weight_ge_fifteen a b hf ha

end
end QldpcVerification.Planar.StripRecurrence
