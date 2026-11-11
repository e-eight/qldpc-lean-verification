import QldpcVerification.Planar.StripLocal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cheap run exits

Local equations from Lemmas 6/7 of `analytical/strip-runs/DRAFT.typ`.
The feeding polynomial is arbitrary, not assumed to be a monomial. We prove
only the necessary weight bound three, not the draft's exact classification.
Cancellation of `1 + X` identifies `X * P`; monomial-shift invariance then
avoids division by X or a lowest-exponent argument.

The long-gap statements use arrays of actual interior pairs in forcing order
(increasing physical index for F, decreasing for B), and sum their actual
excess. They do not assume that excess equals a supplied certificate value.
Physical-index recurrence adapters and global run accounting are out of scope.
Author design checks only; no independent source review or Lean run claimed.
Replay the companion audit with the root agent's detached capped runner.
-/

namespace QldpcVerification.Planar.StripRunLocal

open Polynomial StripLocal
open scoped CharTwo

noncomputable section

private theorem eval_one_singleton {p : P} (hp : wt p = 1) : p.eval 1 = 1 := by
  rw [eval_one_eq_weight, hp]
  rfl

/-- If adding one monomial to t times a monomial leaves a singleton,
it must cancel one of the two terms. No supports are enumerated. -/
theorem singleton_cancellation (a b : P) (ha : wt a = 1) (hb : wt b = 1)
    (hc : wt (t * a + b) = 1) : b = X * a ∨ b = s * a := by
  obtain ⟨n, rfl⟩ := singleton_monomial ha
  obtain ⟨m, rfl⟩ := singleton_monomial hb
  have he : t * (X : P) ^ n + X ^ m = X ^ (n + 1) + X ^ (n + 2) + X ^ m := by
    simp only [t, pow_add]
    ring
  by_cases hm1 : m = n + 1
  · left
    rw [hm1, pow_add]
    ring
  by_cases hm2 : m = n + 2
  · right
    rw [hm2]
    simp only [s, pow_add]
    ring
  have h12 : n + 1 ≠ n + 2 := by omega
  have hsub : ({n + 1, n + 2} : Finset ℕ) ⊆
      (t * (X : P) ^ n + X ^ m).support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · apply Polynomial.mem_support_iff.mpr
      rw [he]
      simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, h12, Ne.symm hm1]
    · apply Polynomial.mem_support_iff.mpr
      rw [he]
      simp [Polynomial.coeff_add, Polynomial.coeff_X_pow, Ne.symm h12, Ne.symm hm2]
  have hcard := Finset.card_le_card hsub
  have htwo : 2 ≤ wt (t * (X : P) ^ n + X ^ m) := by
    simpa [wt, h12] using hcard
  omega

private theorem one_add_X_ne_zero : (1 + X : P) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : P => f.coeff 0) h
  norm_num at hc

private theorem wt_three_terms : wt (1 + X + X ^ 2 : P) = 3 := by
  simpa [wt] using
    (Polynomial.card_support_trinomial (R := ZMod 2)
      (k := 0) (m := 1) (n := 2) (x := 1) (y := 1) (z := 1)
      (by omega) (by omega) one_ne_zero one_ne_zero one_ne_zero)

private theorem three_le_wt_four_terms : 3 ≤ wt (1 + X + X ^ 2 + X ^ 3 : P) := by
  have hsub : ({0, 1, 2} : Finset ℕ) ⊆ (1 + X + X ^ 2 + X ^ 3 : P).support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      norm_num [Polynomial.mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_X_pow,
        Polynomial.coeff_one, Polynomial.coeff_X]
  have hc := Finset.card_le_card hsub
  simpa [wt] using hc

/-- Algebraic core: a singleton residual after t*a+b forces any feed to
have weight at least three. The feed P has no support/degree hypothesis. -/
theorem feed_weight_ge_three (p a b : P) (ha : wt a = 1) (hb : wt b = 1)
    (hfeed : a + s * b = t * p) (hres : wt (t * a + b) = 1) : 3 ≤ wt p := by
  have hcancel := singleton_cancellation a b ha hb hres
  obtain ⟨n, hn⟩ := singleton_monomial ha
  have hshift : wt (X * p) = wt p := by simpa using wt_X_pow_mul p 1
  rcases hcancel with hb | hb
  · have he : (1 + X) * (X * p) = (1 + X) * ((1 + X + X ^ 2) * a) := by
      rw [hb] at hfeed
      dsimp [s, t] at hfeed ⊢
      linear_combination (norm := (ring_nf <;> simp)) -hfeed
    have hp := mul_left_cancel₀ one_add_X_ne_zero he
    rw [hp, hn, wt_mul_X_pow, wt_three_terms] at hshift
    omega
  · have he : (1 + X) * (X * p) =
        (1 + X) * ((1 + X + X ^ 2 + X ^ 3) * a) := by
      rw [hb] at hfeed
      dsimp [s, t] at hfeed ⊢
      linear_combination (norm := (ring_nf <;> simp)) -hfeed
    have hp := mul_left_cancel₀ one_add_X_ne_zero he
    rw [hp, hn, wt_mul_X_pow] at hshift
    have hw := three_le_wt_four_terms
    omega

/-- Lemma 6, F: the actual first three exit weights 2,1,1 force feed weight ≥3. -/
theorem cheap_exit_forward (p a0 b0 a1 b1 a2 b2 : P)
    (w0 : pairWt a0 b0 = 2) (w1 : pairWt a1 b1 = 1) (w2 : pairWt a2 b2 = 1)
    (h0 : a0 + s * b0 = t * p)
    (h1 : a1 + s * b1 = b0)
    (h2 : a2 + s * b2 = t * a0 + b0 + b1) : 3 ≤ wt p := by
  have wb0 : wt b0 = 1 := by simpa only [h1] using singleton_forward w1
  have wa0 : wt a0 = 1 := by unfold pairWt at w0; omega
  have hb1 : b1 = 0 := by
    rcases singleton_blocks w1 with ⟨_, hb1⟩ | ⟨_, wb1⟩
    · exact hb1
    · have he := congrArg (Polynomial.eval (1 : ZMod 2)) h2
      rw [eval_one_singleton (singleton_forward w2)] at he
      simp [t, eval_one_singleton wb0, eval_one_singleton wb1] at he
  have hres : wt (t * a0 + b0) = 1 := by
    have hs := singleton_forward w2
    rw [h2, hb1, add_zero] at hs
    exact hs
  exact feed_weight_ge_three p a0 b0 wa0 wb0 h0 hres

/-- Lemma 6, B: separate feed equations in decreasing physical-index order. -/
theorem cheap_exit_backward (p a0 b0 a1 b1 a2 b2 : P)
    (w0 : pairWt a0 b0 = 2) (w1 : pairWt a1 b1 = 1) (w2 : pairWt a2 b2 = 1)
    (h0 : s * a0 + b0 = t * p)
    (h1 : s * a1 + b1 = s * a0)
    (h2 : s * a2 + b2 = t * b0 + a0 + s * a1) : 3 ≤ wt p := by
  have wa0 : wt a0 = 1 := by simpa only [h1, wt_s_mul] using singleton_backward w1
  have wb0 : wt b0 = 1 := by unfold pairWt at w0; omega
  have ha1 : a1 = 0 := by
    rcases singleton_blocks w1 with ⟨wa1, _⟩ | ⟨ha1, _⟩
    · have he := congrArg (Polynomial.eval (1 : ZMod 2)) h2
      rw [eval_one_singleton (singleton_backward w2)] at he
      simp [t, s, eval_one_singleton wa0, eval_one_singleton wa1] at he
    · exact ha1
  have hres : wt (t * b0 + a0) = 1 := by
    have hs := singleton_backward w2
    rw [h2, ha1, mul_zero, add_zero] at hs
    exact hs
  exact feed_weight_ge_three p b0 a0 wb0 wa0 (by simpa [add_comm] using h0) hres

/-- Excess of the first three actual exit slices. -/
def exitExcess (a0 b0 a1 b1 a2 b2 : P) : ℕ :=
  (pairWt a0 b0 - 1) + (pairWt a1 b1 - 1) + (pairWt a2 b2 - 1)

/-- Lemma 7 already holds on the first three slices, in the F orientation. -/
theorem exit_alternative_forward (p a0 b0 a1 b1 a2 b2 : P) (hp : p ≠ 0)
    (w1 : 1 ≤ pairWt a1 b1) (w2 : 1 ≤ pairWt a2 b2)
    (h0 : a0 + s * b0 = t * p)
    (h1 : a1 + s * b1 = b0)
    (h2 : a2 + s * b2 = t * a0 + b0 + b1) :
    2 ≤ exitExcess a0 b0 a1 b1 a2 b2 ∨ 3 ≤ wt p := by
  have hheavy : 2 ≤ pairWt a0 b0 := by
    have hl := two_le_wt_t_mul hp
    have hu := wt_add_le a0 (s * b0)
    rw [h0, wt_s_mul] at hu
    unfold pairWt
    omega
  by_cases hex : 2 ≤ exitExcess a0 b0 a1 b1 a2 b2
  · exact Or.inl hex
  · right
    unfold exitExcess at hex
    exact cheap_exit_forward p a0 b0 a1 b1 a2 b2
      (by omega) (by omega) (by omega) h0 h1 h2

/-- Lemma 7 on the first three slices, in the B orientation. -/
theorem exit_alternative_backward (p a0 b0 a1 b1 a2 b2 : P) (hp : p ≠ 0)
    (w1 : 1 ≤ pairWt a1 b1) (w2 : 1 ≤ pairWt a2 b2)
    (h0 : s * a0 + b0 = t * p)
    (h1 : s * a1 + b1 = s * a0)
    (h2 : s * a2 + b2 = t * b0 + a0 + s * a1) :
    2 ≤ exitExcess a0 b0 a1 b1 a2 b2 ∨ 3 ≤ wt p := by
  have hheavy : 2 ≤ pairWt a0 b0 := by
    have hl := two_le_wt_t_mul hp
    have hu := wt_add_le (s * a0) b0
    rw [h0, wt_s_mul] at hu
    unfold pairWt
    omega
  by_cases hex : 2 ≤ exitExcess a0 b0 a1 b1 a2 b2
  · exact Or.inl hex
  · right
    unfold exitExcess at hex
    exact cheap_exit_backward p a0 b0 a1 b1 a2 b2
      (by omega) (by omega) (by omega) h0 h1 h2

/-- Actual interior excess of a gap of length d. Arrays are in forcing order,
starting at the exit target (interior index zero). -/
def interiorExcess (a b : ℕ → P) (d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d - 1), (pairWt (a i) (b i) - 1)

/-- The first three interior sites form a subset of every gap of length ≥4. -/
theorem exitExcess_le_interior (a b : ℕ → P) (d : ℕ) (hd : 4 ≤ d) :
    exitExcess (a 0) (b 0) (a 1) (b 1) (a 2) (b 2) ≤ interiorExcess a b d := by
  have hsum : (∑ i ∈ Finset.range 3, (pairWt (a i) (b i) - 1)) ≤
      ∑ i ∈ Finset.range (d - 1), (pairWt (a i) (b i) - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (by omega)
    · intros
      exact Nat.zero_le _
  simpa [exitExcess, interiorExcess, Finset.sum_range_succ] using hsum

/-- Longer-gap exit alternative for F, with the excess actually summed. -/
theorem longer_gap_exit_forward (p : P) (a b : ℕ → P) (d : ℕ) (hd : 4 ≤ d)
    (hp : p ≠ 0) (ho : ∀ i, i < d - 1 → 1 ≤ pairWt (a i) (b i))
    (h0 : a 0 + s * b 0 = t * p)
    (h1 : a 1 + s * b 1 = b 0)
    (h2 : a 2 + s * b 2 = t * a 0 + b 0 + b 1) :
    2 ≤ interiorExcess a b d ∨ 3 ≤ wt p := by
  rcases exit_alternative_forward p (a 0) (b 0) (a 1) (b 1) (a 2) (b 2)
    hp (ho 1 (by omega)) (ho 2 (by omega)) h0 h1 h2 with hex | hpw
  · exact Or.inl (hex.trans (exitExcess_le_interior a b d hd))
  · exact Or.inr hpw

/-- Longer-gap exit alternative for B, with arrays in decreasing physical order. -/
theorem longer_gap_exit_backward (p : P) (a b : ℕ → P) (d : ℕ) (hd : 4 ≤ d)
    (hp : p ≠ 0) (ho : ∀ i, i < d - 1 → 1 ≤ pairWt (a i) (b i))
    (h0 : s * a 0 + b 0 = t * p)
    (h1 : s * a 1 + b 1 = s * a 0)
    (h2 : s * a 2 + b 2 = t * b 0 + a 0 + s * a 1) :
    2 ≤ interiorExcess a b d ∨ 3 ≤ wt p := by
  rcases exit_alternative_backward p (a 0) (b 0) (a 1) (b 1) (a 2) (b 2)
    hp (ho 1 (by omega)) (ho 2 (by omega)) h0 h1 h2 with hex | hpw
  · exact Or.inl (hex.trans (exitExcess_le_interior a b d hd))
  · exact Or.inr hpw

/-- The length-three exception needs no feed hypothesis, in F. -/
theorem gap_three_excess_forward (p q u v : P)
    (h1 : u = q + s * v) (h2 : t * p + q + v = 0)
    (w1 : 1 ≤ pairWt p q) (w2 : 1 ≤ pairWt u v) :
    2 ≤ (pairWt p q - 1) + (pairWt u v - 1) := by
  have hc := gap_three_forward p q u v h1 h2 (by omega)
  omega

/-- The length-three exception needs no feed hypothesis, in B. -/
theorem gap_three_excess_backward (p q u v : P)
    (h1 : t * v = u + s * p) (h2 : q = s * (u + p))
    (w1 : 1 ≤ pairWt p q) (w2 : 1 ≤ pairWt u v) :
    2 ≤ (pairWt p q - 1) + (pairWt u v - 1) := by
  have hc := gap_three_backward p q u v h1 h2 (by omega)
  omega

end
end QldpcVerification.Planar.StripRunLocal
