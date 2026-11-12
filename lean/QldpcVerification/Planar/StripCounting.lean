import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Analytic strip counting

This is the global combinatorial step of `analytical/strip-deficits/DRAFT.tex`.
Weights are arbitrary natural numbers; the polynomial local lemmas are inputs.
All counts below are sums over the actual sequence, not certificate parameters.

The decomposition is constructed in `span_budget`: after an occupied site we
advance one site; after a zero we choose the *first* subsequent zero. Thus the
interiors charged in successive recursive calls are disjoint. For each gap of
length `d`, the combined span/interior inequality is
`6 ≤ d + 4 * [d = 2] + 2 * (interior excess)`.
This sums the draft's H/K/L budgets without introducing three separate counters.
The length-two counter is charged separately to distinct shifted target sites.
Overlap between these two budgets is permitted and accounted for explicitly.

No enumeration of weight sequences, computational certificate, or native
decision procedure is used. The final rounding is integer linear arithmetic.
-/

namespace QldpcVerification.Planar.StripCounting

open Finset

/-- Sum on a half-open interval of physical indices. -/
def intervalSum (f : ℕ → ℕ) (a b : ℕ) : ℕ := ∑ i ∈ Ico a b, f i

/-- Zero indicator and excess above the first unit of weight. -/
def zeroIndicator (w : ℕ → ℕ) (i : ℕ) : ℕ := if w i = 0 then 1 else 0

def excess (w : ℕ → ℕ) (i : ℕ) : ℕ := w i - 1

/-- A genuine length-two gap starting at `i`, with both ends inside the strip.
Adjacent nonemptiness ensures its interior is occupied. -/
def shortIndicator (w : ℕ → ℕ) (n i : ℕ) : ℕ :=
  if w i = 0 ∧ i + 2 < n ∧ w (i + 2) = 0 then 1 else 0

/-- Occupancy of the open interval between two successive zeros. -/
def Occupied (w : ℕ → ℕ) (a b : ℕ) : Prop :=
  ∀ i, a < i → i < b → 0 < w i

/-- Local hypotheses only. The gap interiors here must actually be occupied;
the global argument constructs this fact rather than assuming a decomposition. -/
structure GapCosts (w : ℕ → ℕ) (n : ℕ) : Prop where
  adjacent : ∀ i, i + 1 < n → 1 ≤ w i + w (i + 1)
  three : ∀ a, a + 3 < n → w a = 0 → w (a + 3) = 0 →
    Occupied w a (a + 3) → 4 ≤ intervalSum w (a + 1) (a + 3)
  four : ∀ a, a + 4 < n → w a = 0 → w (a + 4) = 0 →
    Occupied w a (a + 4) → 4 ≤ intervalSum w (a + 1) (a + 4)
  five : ∀ a, a + 5 < n → w a = 0 → w (a + 5) = 0 →
    Occupied w a (a + 5) → 5 ≤ intervalSum w (a + 1) (a + 5)

/-- Forward branch: the target is three sites after the left zero. The gap
starting at 16 in a 19-site strip is the sole possible boundary exception. -/
def ForwardBranch (w : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ a, a + 3 < n → w a = 0 → w (a + 2) = 0 → 2 ≤ w (a + 3)

/-- Backward branch: the target is one site before the left zero. Only the
gap starting at zero can escape this charge. -/
def BackwardBranch (w : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ a, 1 ≤ a → a + 2 < n → w a = 0 → w (a + 2) = 0 → 2 ≤ w (a - 1)

theorem intervalSum_split (f : ℕ → ℕ) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    intervalSum f a c = intervalSum f a b + intervalSum f b c := by
  exact (Finset.sum_Ico_consecutive f hab hbc).symm

theorem intervalSum_head (f : ℕ → ℕ) {a b : ℕ} (hab : a < b) :
    intervalSum f a b = f a + intervalSum f (a + 1) b := by
  exact Finset.sum_eq_sum_Ico_succ_bot hab f

theorem intervalSum_mono (f : ℕ → ℕ) {a b c d : ℕ}
    (hac : a ≤ c) (hdb : d ≤ b) : intervalSum f c d ≤ intervalSum f a b := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    simp only [mem_Ico] at hi ⊢
    omega
  · intros
    exact Nat.zero_le _

/-- On an occupied interval the baseline is exactly its number of sites. -/
theorem occupied_mass (w : ℕ → ℕ) {a b : ℕ}
    (h : ∀ i, a ≤ i → i < b → 0 < w i) :
    intervalSum w a b = (b - a) + intervalSum (excess w) a b := by
  have heq : intervalSum w a b = ∑ i ∈ Ico a b, (1 + excess w i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hp := h i (mem_Ico.mp hi).1 (mem_Ico.mp hi).2
    dsimp [excess]
    omega
  simpa [intervalSum, Finset.sum_add_distrib] using heq

/-- The exact mass/zero/excess identity, including empty sites. -/
theorem mass_identity (w : ℕ → ℕ) (a b : ℕ) :
    intervalSum w a b + intervalSum (zeroIndicator w) a b =
      (b - a) + intervalSum (excess w) a b := by
  have hpoint : ∀ i, w i + zeroIndicator w i = 1 + excess w i := by
    intro i
    by_cases hi : w i = 0
    · simp [zeroIndicator, excess, hi]
    · simp only [zeroIndicator, if_neg hi, excess]
      omega
  unfold intervalSum
  rw [← Finset.sum_add_distrib]
  simp_rw [hpoint]
  simp [Finset.sum_add_distrib]

/-- A constructed successive-zero gap contains exactly one zero in `[a,b)`. -/
theorem gap_zero_count (w : ℕ → ℕ) {a b : ℕ} (hab : a < b)
    (ha : w a = 0) (hocc : Occupied w a b) :
    intervalSum (zeroIndicator w) a b = 1 := by
  unfold intervalSum
  rw [Finset.sum_eq_single a]
  · simp [zeroIndicator, ha]
  · intro i hi hia
    have hp := hocc i (by have := (mem_Ico.mp hi).1; omega) (mem_Ico.mp hi).2
    simp [zeroIndicator, Nat.ne_of_gt hp]
  · intro h
    exact False.elim (h (mem_Ico.mpr ⟨le_rfl, hab⟩))

/-- The only possible length-two gap starting in this half-open gap is the
gap itself. This proves the counting multiplicity from actual zero positions. -/
theorem gap_short_count (w : ℕ → ℕ) {n a b : ℕ}
    (hab : a < b) (hb : b < n) (ha0 : w a = 0) (hb0 : w b = 0)
    (hocc : Occupied w a b) (hsep : a + 2 ≤ b) :
    intervalSum (shortIndicator w n) a b = if b = a + 2 then 1 else 0 := by
  unfold intervalSum
  rw [Finset.sum_eq_single a]
  · by_cases heq : b = a + 2
    · subst b
      simp [shortIndicator, ha0, hb0, hb]
    · have hp := hocc (a + 2) (by omega) (by omega)
      simp [shortIndicator, Nat.ne_of_gt hp, heq]
  · intro i hi hia
    have hp := hocc i (by have := (mem_Ico.mp hi).1; omega) (mem_Ico.mp hi).2
    simp [shortIndicator, Nat.ne_of_gt hp]
  · intro h
    exact False.elim (h (mem_Ico.mpr ⟨le_rfl, hab⟩))

/-- Local weighted span cost. Only the four symbolic length classes 2,3,4,5
need special inequalities; every length at least six pays its own span cost. -/
theorem gap_span_cost (w : ℕ → ℕ) {n a b : ℕ} (costs : GapCosts w n)
    (hab : a < b) (hb : b < n) (ha0 : w a = 0) (hb0 : w b = 0)
    (hocc : Occupied w a b) :
    6 ≤ (b - a) + 4 * intervalSum (shortIndicator w n) a b +
      2 * intervalSum (excess w) a b := by
  have hsep : a + 2 ≤ b := by
    by_contra hh
    have heq : b = a + 1 := by omega
    have hadj := costs.adjacent a (by omega)
    rw [← heq, ha0, hb0] at hadj
    omega
  rw [gap_short_count w hab hb ha0 hb0 hocc hsep]
  have hmass := occupied_mass w (a := a + 1) (b := b)
    (fun i hi hib => hocc i (by omega) hib)
  have hex : intervalSum (excess w) a b = intervalSum (excess w) (a + 1) b := by
    rw [intervalSum_head _ hab]
    simp [excess, ha0]
  by_cases h2 : b = a + 2
  · simp only [if_pos h2]
    omega
  simp only [if_neg h2, mul_zero, add_zero]
  by_cases h3 : b = a + 3
  · have hc := costs.three a (by omega) ha0 (by simpa [← h3] using hb0)
      (by simpa [← h3] using hocc)
    rw [← h3] at hc
    omega
  by_cases h4 : b = a + 4
  · have hc := costs.four a (by omega) ha0 (by simpa [← h4] using hb0)
      (by simpa [← h4] using hocc)
    rw [← h4] at hc
    omega
  by_cases h5 : b = a + 5
  · have hc := costs.five a (by omega) ha0 (by simpa [← h5] using hb0)
      (by simpa [← h5] using hocc)
    rw [← h5] at hc
    omega
  omega

/-- Construct the gap decomposition of an arbitrary actual sequence. The
first subsequent zero is chosen by `Nat.find`; no gap data are supplied.

The constant five covers the final zero and any occupied terminal tail.
Splitting half-open intervals proves that every interior excess is used once.
-/
theorem span_budget (w : ℕ → ℕ) {n : ℕ} (costs : GapCosts w n)
    (a : ℕ) (ha : a ≤ n) :
    6 * intervalSum (zeroIndicator w) a n ≤ (n - a) + 5 +
      4 * intervalSum (shortIndicator w n) a n + 2 * intervalSum (excess w) a n := by
  classical
  suffices ∀ d a, n - a = d → a ≤ n →
      6 * intervalSum (zeroIndicator w) a n ≤ (n - a) + 5 +
        4 * intervalSum (shortIndicator w n) a n +
        2 * intervalSum (excess w) a n from this (n - a) a rfl ha
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hda han
    by_cases heq : a = n
    · subst a
      simp [intervalSum]
    have han' : a < n := by omega
    by_cases ha0 : w a = 0
    · by_cases hnxt : ∃ b, a < b ∧ b < n ∧ w b = 0
      · let b := Nat.find hnxt
        have hb := Nat.find_spec hnxt
        change a < b ∧ b < n ∧ w b = 0 at hb
        have hocc : Occupied w a b := by
          intro i hai hib
          by_contra hi
          have hi0 : w i = 0 := by omega
          have hmin : b ≤ i := Nat.find_min' hnxt ⟨hai, by omega, hi0⟩
          omega
        have hgap := gap_span_cost w costs hb.1 hb.2.1 ha0 hb.2.2 hocc
        have hz := gap_zero_count w hb.1 ha0 hocc
        have htail := ih (n - b) (by omega) b rfl (by omega)
        rw [intervalSum_split _ (by omega : a ≤ b) (by omega : b ≤ n), hz]
        rw [intervalSum_split (shortIndicator w n) (by omega : a ≤ b)
          (by omega : b ≤ n)]
        rw [intervalSum_split (excess w) (by omega : a ≤ b) (by omega : b ≤ n)]
        omega
      · have hocc : Occupied w a n := by
          intro i hai hin
          by_contra hi
          exact hnxt ⟨i, hai, hin, by omega⟩
        rw [gap_zero_count w han' ha0 hocc]
        omega
    · have htail := ih (n - (a + 1)) (by omega) (a + 1) rfl (by omega)
      have hzhead : zeroIndicator w a = 0 := by simp [zeroIndicator, ha0]
      have hghead : shortIndicator w n a = 0 := by simp [shortIndicator, ha0]
      rw [intervalSum_head _ han', intervalSum_head (shortIndicator w n) han',
        intervalSum_head (excess w) han', hzhead, hghead]
      omega

/-- Forward charging uses the injective translation `i ↦ i+3`. The interval
translation identity records multiplicity one, including for heavy middles. -/
theorem forward_branch_budget (w : ℕ → ℕ) (branch : ForwardBranch w 19) :
    intervalSum (shortIndicator w 19) 0 19 ≤ intervalSum (excess w) 0 19 + 1 := by
  have hmain : intervalSum (shortIndicator w 19) 0 16 ≤
      ∑ i ∈ Ico 0 16, excess w (i + 3) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := mem_Ico.mp hi
    by_cases h : w i = 0 ∧ i + 2 < 19 ∧ w (i + 2) = 0
    · have ht := branch i (by omega) h.1 h.2.2
      simp only [shortIndicator, if_pos h, excess]
      omega
    · simp [shortIndicator, h]
  have hshift : (∑ i ∈ Ico 0 16, excess w (i + 3)) = intervalSum (excess w) 3 19 := by
    exact Finset.sum_Ico_add' (excess w) 0 16 3
  have hsub := intervalSum_mono (excess w) (a := 0) (b := 19)
    (c := 3) (d := 19) (by omega) (by omega)
  have hlast : intervalSum (shortIndicator w 19) 16 19 ≤ 1 := by
    have heq : intervalSum (shortIndicator w 19) 16 19 = shortIndicator w 19 16 := by
      unfold intervalSum
      apply Finset.sum_eq_single
      · intro i hi hne
        have hi' := mem_Ico.mp hi
        have hn : ¬ i + 2 < 19 := by omega
        simp [shortIndicator, hn]
      · simp
    rw [heq]
    unfold shortIndicator
    split_ifs <;> omega
  rw [intervalSum_split _ (by omega : 0 ≤ 16) (by omega : 16 ≤ 19)]
  omega

/-- Backward charging uses the injective translation `i ↦ i-1` on `i≥1`.
This proves the reverse-direction budget directly, without changing indices
in the local gap hypotheses. -/
theorem backward_branch_budget (w : ℕ → ℕ) (branch : BackwardBranch w 19) :
    intervalSum (shortIndicator w 19) 0 19 ≤ intervalSum (excess w) 0 19 + 1 := by
  have hmain : intervalSum (shortIndicator w 19) 1 19 ≤
      ∑ i ∈ Ico 1 19, excess w (i - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := mem_Ico.mp hi
    by_cases h : w i = 0 ∧ i + 2 < 19 ∧ w (i + 2) = 0
    · have ht := branch i hi'.1 h.2.1 h.1 h.2.2
      simp only [shortIndicator, if_pos h, excess]
      omega
    · simp [shortIndicator, h]
  have hshift : (∑ i ∈ Ico 1 19, excess w (i - 1)) = intervalSum (excess w) 0 18 := by
    exact Finset.sum_Ico_add_right_sub_eq (f := excess w) 0 18 1
  have hsub := intervalSum_mono (excess w) (a := 0) (b := 19)
    (c := 0) (d := 18) (by omega) (by omega)
  have hfirst : shortIndicator w 19 0 ≤ 1 := by
    unfold shortIndicator
    split_ifs <;> omega
  rw [hshift] at hmain
  rw [intervalSum_head _ (by omega : 0 < 19)]
  change shortIndicator w 19 0 + intervalSum (shortIndicator w 19) 1 19 ≤
    intervalSum (excess w) 0 19 + 1
  omega

/-- Combine the constructed decomposition with either directional budget.
The two uses of excess need not be disjoint: their coefficients add to six. -/
theorem weight_ge_fifteen_of_branch_budget (w : ℕ → ℕ) (costs : GapCosts w 19)
    (budget : intervalSum (shortIndicator w 19) 0 19 ≤
      intervalSum (excess w) 0 19 + 1) :
    15 ≤ intervalSum w 0 19 := by
  have hspan := span_budget w costs 0 (by omega)
  have hmass := mass_identity w 0 19
  omega

/-- Nineteen weights with the forward local branch and gap costs total at
least fifteen. All gap counts and charging multiplicities are derived above. -/
theorem weight_ge_fifteen_forward (w : ℕ → ℕ) (costs : GapCosts w 19)
    (branch : ForwardBranch w 19) : 15 ≤ intervalSum w 0 19 := by
  exact weight_ge_fifteen_of_branch_budget w costs (forward_branch_budget w branch)

/-- The same analytic bound for the backward local branch. -/
theorem weight_ge_fifteen_backward (w : ℕ → ℕ) (costs : GapCosts w 19)
    (branch : BackwardBranch w 19) : 15 ≤ intervalSum w 0 19 := by
  exact weight_ge_fifteen_of_branch_budget w costs (backward_branch_budget w branch)

end QldpcVerification.Planar.StripCounting
