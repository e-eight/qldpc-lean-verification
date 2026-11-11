import QldpcVerification.Planar.StripRunLocal

/-!
# Exact cheap-exit feed forms

The strong conclusion of Lemma 6 in the frozen strip-runs paper: any feeding
polynomial for an exit of weights 2,1,1 is a monomial shift of three or four
consecutive terms. The hypotheses and the separate F/B equations agree with
StripRunLocal.cheap_exit_forward/backward; the feed is arbitrary.

This strengthens only the local classification, not a distance bound.
Author design checks only; no independent source review or local Lean run.
All checked prerequisite files remain unchanged. Root capped replay required.
-/

namespace QldpcVerification.Planar.StripRunClassification

open Polynomial StripLocal StripRunLocal
open scoped CharTwo

noncomputable section

private theorem one_add_X_ne_zero : (1 + X : P) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : P => f.coeff 0) h
  norm_num at hc

/-- A polynomial with constant coefficient one cannot absorb the X on the
left at exponent zero. For positive exponent, cancel X in the domain. -/
private theorem cancel_shift (p f : P) (hf : f.coeff 0 = 1) (k : ℕ)
    (he : X * p = f * X ^ k) : ∃ n, p = f * X ^ n := by
  cases k with
  | zero =>
    have hc := congrArg (fun q : P => q.coeff 0) he
    norm_num [Polynomial.coeff_X_mul_zero, hf] at hc
  | succ n =>
    refine ⟨n, mul_left_cancel₀ Polynomial.X_ne_zero ?_⟩
    calc
      X * p = f * X ^ (n + 1) := he
      _ = X * (f * X ^ n) := by rw [pow_succ]; ring

/-- Generic exact feed classification. The singleton hypotheses concern the
exit blocks a,b, never the feeding polynomial p. -/
theorem feed_normal_forms (p a b : P) (ha : wt a = 1) (hb : wt b = 1)
    (hfeed : a + s * b = t * p) (hres : wt (t * a + b) = 1) :
    ∃ n : ℕ, p = (1 + X + X ^ 2) * X ^ n ∨
      p = (1 + X + X ^ 2 + X ^ 3) * X ^ n := by
  have hcancel := singleton_cancellation a b ha hb hres
  obtain ⟨k, hk⟩ := singleton_monomial ha
  rcases hcancel with hb | hb
  · have he : (1 + X) * (X * p) = (1 + X) * ((1 + X + X ^ 2) * a) := by
      rw [hb] at hfeed
      dsimp [s, t] at hfeed ⊢
      linear_combination (norm := (ring_nf <;> simp)) -hfeed
    have hp := mul_left_cancel₀ one_add_X_ne_zero he
    rw [hk] at hp
    obtain ⟨n, hn⟩ := cancel_shift p (1 + X + X ^ 2)
      (by norm_num [Polynomial.coeff_add, Polynomial.coeff_one,
        Polynomial.coeff_X, Polynomial.coeff_X_pow]) k hp
    exact ⟨n, Or.inl hn⟩
  · have he : (1 + X) * (X * p) =
        (1 + X) * ((1 + X + X ^ 2 + X ^ 3) * a) := by
      rw [hb] at hfeed
      dsimp [s, t] at hfeed ⊢
      linear_combination (norm := (ring_nf <;> simp)) -hfeed
    have hp := mul_left_cancel₀ one_add_X_ne_zero he
    rw [hk] at hp
    obtain ⟨n, hn⟩ := cancel_shift p (1 + X + X ^ 2 + X ^ 3)
      (by norm_num [Polynomial.coeff_add, Polynomial.coeff_one,
        Polynomial.coeff_X, Polynomial.coeff_X_pow]) k hp
    exact ⟨n, Or.inr hn⟩

private theorem eval_one_singleton {p : P} (hp : wt p = 1) : p.eval 1 = 1 := by
  rw [eval_one_eq_weight, hp]
  rfl

/-- Exact Lemma 6 for F, from the same weights and equations as the checked
cheap_exit_forward lower bound. All shifts are ordinary natural exponents. -/
theorem cheap_exit_forward_normal_forms (p a0 b0 a1 b1 a2 b2 : P)
    (w0 : pairWt a0 b0 = 2) (w1 : pairWt a1 b1 = 1) (w2 : pairWt a2 b2 = 1)
    (h0 : a0 + s * b0 = t * p)
    (h1 : a1 + s * b1 = b0)
    (h2 : a2 + s * b2 = t * a0 + b0 + b1) :
    ∃ n : ℕ, p = (1 + X + X ^ 2) * X ^ n ∨
      p = (1 + X + X ^ 2 + X ^ 3) * X ^ n := by
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
  exact feed_normal_forms p a0 b0 wa0 wb0 h0 hres

/-- Exact Lemma 6 for B, with its own equations in decreasing physical order.
No transformation of the F recurrence is assumed. -/
theorem cheap_exit_backward_normal_forms (p a0 b0 a1 b1 a2 b2 : P)
    (w0 : pairWt a0 b0 = 2) (w1 : pairWt a1 b1 = 1) (w2 : pairWt a2 b2 = 1)
    (h0 : s * a0 + b0 = t * p)
    (h1 : s * a1 + b1 = s * a0)
    (h2 : s * a2 + b2 = t * b0 + a0 + s * a1) :
    ∃ n : ℕ, p = (1 + X + X ^ 2) * X ^ n ∨
      p = (1 + X + X ^ 2 + X ^ 3) * X ^ n := by
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
  exact feed_normal_forms p b0 a0 wb0 wa0 (by simpa [add_comm] using h0) hres

end
end QldpcVerification.Planar.StripRunClassification
