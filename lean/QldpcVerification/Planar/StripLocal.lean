import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Local polynomial strip costs

Local equations of `analytical/strip-deficits/DRAFT.typ`, over ordinary
polynomials (no quotient, degree cutoff, or enumeration of codewords).
The gap names count the distance between zero slices, not the interior size.
F arguments are in increasing order; B gap-five arguments are in decreasing
order. The B gap-three and gap-four arguments are in increasing order.

Author design checks (not independent source review):
1. Algebra: F and B equations checked separately against the draft. The
   gap-three zero-block case uses derivative evaluation at one, avoiding
   division by X and the unformalized run-count identity.
2. Hypotheses: gap three only needs a nonempty interior; gap four needs all
   three occupied; gap five needs four occupied and only its directional zero.
   Branch targets require an available second equation; no endpoint extension.
3. Soundness boundary: all local costs below have polynomial proofs, without
   new axiom declarations, `sorry`, finite-support search, or assumed weight
   inequalities. Standard propext/Classical.choice/Quot.sound are permitted.
   The global disjoint-gap/branch counting argument and recurrence adapters
   are outside this file. No Lean process was run by this file's author;
   the companion guarded audit must be replayed by the detached capped runner.
-/

namespace QldpcVerification.Planar.StripLocal

open Polynomial
open scoped CharTwo

noncomputable section

abbrev P := Polynomial (ZMod 2)

def wt (p : P) : ℕ := p.support.card

def pairWt (a b : P) : ℕ := wt a + wt b

def t : P := X + X ^ 2

def s : P := X ^ 2

@[simp] theorem wt_zero : wt 0 = 0 := by simp [wt]

@[simp] theorem wt_eq_zero {p : P} : wt p = 0 ↔ p = 0 :=
  Polynomial.card_support_eq_zero

theorem wt_pos {p : P} (hp : p ≠ 0) : 1 ≤ wt p := by
  have : wt p ≠ 0 := fun h => hp (wt_eq_zero.mp h)
  omega

@[simp] theorem wt_X_pow (n : ℕ) : wt (X ^ n) = 1 := by
  simp [wt, Polynomial.support_X_pow one_ne_zero]

/-- Multiplication by a monomial shifts support injectively. -/
@[simp] theorem wt_mul_X_pow (p : P) (n : ℕ) : wt (p * X ^ n) = wt p := by
  apply le_antisymm
  · have h := Polynomial.card_support_mul_le (p := p) (q := (X : P) ^ n)
    simpa only [wt, Polynomial.support_X_pow one_ne_zero,
      Finset.card_singleton, mul_one] using h
  · change p.support.card ≤ (p * X ^ n).support.card
    apply Finset.card_le_card_of_injOn (fun i => i + n)
    · intro i hi
      change i ∈ p.support at hi
      change i + n ∈ (p * X ^ n).support
      apply Polynomial.mem_support_iff.mpr
      rw [Polynomial.coeff_mul_X_pow p n i]
      exact Polynomial.mem_support_iff.mp hi
    · intro i _ j _ hij
      exact Nat.add_right_cancel hij

@[simp] theorem wt_X_pow_mul (p : P) (n : ℕ) : wt (X ^ n * p) = wt p := by
  rw [mul_comm, wt_mul_X_pow]

@[simp] theorem wt_s_mul (p : P) : wt (s * p) = wt p := wt_X_pow_mul p 2

@[simp] theorem s_ne_zero : s ≠ 0 := pow_ne_zero 2 Polynomial.X_ne_zero

@[simp] theorem s_mul_eq_zero {p : P} : s * p = 0 ↔ p = 0 := by
  simp only [mul_eq_zero, s_ne_zero, false_or]

theorem wt_add_le (p q : P) : wt (p + q) ≤ wt p + wt q :=
  (Finset.card_le_card Polynomial.support_add).trans (Finset.card_union_le _ _)

/-- Over F₂, evaluation at one is precisely the coefficient-count parity. -/
theorem eval_one_eq_weight (p : P) : p.eval 1 = (wt p : ZMod 2) := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  calc
    (∑ i ∈ p.support, p.coeff i * (1 : ZMod 2) ^ i) =
        ∑ _i ∈ p.support, (1 : ZMod 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hc0 : p.coeff i ≠ (0 : ZMod 2) := Polynomial.mem_support_iff.mp hi
      have hc : p.coeff i = 1 := Fin.eq_one_of_ne_zero _ hc0
      simp [hc]
    _ = (wt p : ZMod 2) := by simp [wt]

/-- Nonzero and even weight excludes both zero and singleton support. -/
theorem two_le_wt_of_eval_one_zero {p : P} (hp : p ≠ 0)
    (he : p.eval 1 = 0) : 2 ≤ wt p := by
  have hpos := wt_pos hp
  by_contra h
  have hw : wt p = 1 := by omega
  rw [eval_one_eq_weight, hw] at he
  norm_num at he

/-- A singleton polynomial is one monomial, with coefficient one. -/
theorem singleton_monomial {p : P} (hp : wt p = 1) : ∃ n, p = X ^ n := by
  obtain ⟨n, c, hc⟩ := Polynomial.card_support_le_one_iff_monomial.mp
    (show p.support.card ≤ 1 by change wt p ≤ 1; omega)
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
    simp [hc] at hp
  have hc1 : c = 1 := Fin.eq_one_of_ne_zero c hc0
  exact ⟨n, by simpa [hc1, Polynomial.X_pow_eq_monomial] using hc⟩

/-- Exactly one block of a singleton slice is a monomial. -/
theorem singleton_pair {a b : P} (h : pairWt a b = 1) :
    (∃ n, a = X ^ n ∧ b = 0) ∨ (∃ n, a = 0 ∧ b = X ^ n) := by
  unfold pairWt at h
  by_cases ha : wt a = 0
  · right
    obtain ⟨n, hn⟩ := singleton_monomial (p := b) (by omega)
    exact ⟨n, wt_eq_zero.mp ha, hn⟩
  · left
    obtain ⟨n, hn⟩ := singleton_monomial (p := a) (by omega)
    exact ⟨n, hn, wt_eq_zero.mp (by omega)⟩

/-- Weight-only form of the singleton classification. -/
theorem singleton_blocks {a b : P} (h : pairWt a b = 1) :
    (wt a = 1 ∧ b = 0) ∨ (a = 0 ∧ wt b = 1) := by
  rcases singleton_pair h with ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ <;> simp

theorem singleton_forward {a b : P} (h : pairWt a b = 1) : wt (a + s * b) = 1 := by
  rcases singleton_blocks h with ⟨ha, rfl⟩ | ⟨rfl, hb⟩
  · simpa using ha
  · simpa using hb

theorem singleton_backward {a b : P} (h : pairWt a b = 1) : wt (s * a + b) = 1 := by
  rcases singleton_blocks h with ⟨ha, rfl⟩ | ⟨rfl, hb⟩
  · simpa using ha
  · simpa using hb

theorem t_ne_zero : t ≠ 0 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 1) h
  norm_num [t] at hc

theorem one_add_s_ne_zero : (1 : P) + s ≠ 0 := by
  intro h
  have hc := congrArg (fun p : P => p.coeff 0) h
  norm_num [s] at hc

/-- The required nonzero*(T+T²) bound: domain nonvanishing plus eval-one parity. -/
theorem two_le_wt_t_mul {p : P} (hp : p ≠ 0) : 2 ≤ wt (t * p) := by
  apply two_le_wt_of_eval_one_zero (mul_ne_zero t_ne_zero hp)
  simp [t]

theorem two_le_wt_mul_t {p : P} (hp : p ≠ 0) : 2 ≤ wt (p * t) := by
  simpa only [mul_comm] using two_le_wt_t_mul hp

theorem two_le_wt_one_add_s_mul {p : P} (hp : p ≠ 0) :
    2 ≤ wt ((1 + s) * p) := by
  apply two_le_wt_of_eval_one_zero (mul_ne_zero one_add_s_ne_zero hp)
  simp [s]

/-- The other terminal pattern has three distinct monomials. -/
theorem wt_terminal {p : P} (hp : wt p = 1) :
    wt ((1 + X ^ 3 + X ^ 4) * p) = 3 := by
  obtain ⟨n, rfl⟩ := singleton_monomial hp
  rw [wt_mul_X_pow]
  simpa [wt] using
    (Polynomial.card_support_trinomial (R := ZMod 2)
      (k := 0) (m := 3) (n := 4) (x := 1) (y := 1) (z := 1)
      (by omega) (by omega) one_ne_zero one_ne_zero one_ne_zero)

/-- Forward branch: equation at r+1 kills b_r; the next equation pays at r+2. -/
theorem branch_forward (p q a b : P) (hkill : q = 0)
    (hnext : a + s * b = t * p) (hocc : 1 ≤ pairWt p q) :
    q = 0 ∧ 2 ≤ pairWt a b := by
  have hp : p ≠ 0 := by intro h; simp [pairWt, h, hkill] at hocc
  have hl := two_le_wt_t_mul hp
  have hu := wt_add_le a (s * b)
  rw [hnext, wt_s_mul] at hu
  exact ⟨hkill, by unfold pairWt; omega⟩

/-- Backward branch: equation at r+1 kills a_r, and equation r pays at r-2. -/
theorem branch_backward (p q a b : P) (hkill : s * p = 0)
    (hprev : s * a + b = t * q) (hocc : 1 ≤ pairWt p q) :
    p = 0 ∧ 2 ≤ pairWt a b := by
  have hp := s_mul_eq_zero.mp hkill
  have hq : q ≠ 0 := by intro h; simp [pairWt, hp, h] at hocc
  have hl := two_le_wt_t_mul hq
  have hu := wt_add_le (s * a) b
  rw [hprev, wt_s_mul] at hu
  exact ⟨hp, by unfold pairWt; omega⟩

/-- Differentiation replaces the run-count/factorization step in a short gap. -/
theorem eval_one_zero_of_t_mul_eq {p v : P} (h : t * p = (1 + s) * v) :
    p.eval 1 = 0 := by
  have hd := congrArg (fun f : P => f.derivative.eval 1) h
  simpa [t, s, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.derivative_X_pow] using hd

/-- A zero sum of three nonzero-multiplier terms cannot have total weight one. -/
theorem three_term_cost (a b c A B C : P)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (he : A * a + B * b + C * c = 0)
    (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : 2 ≤ wt a + wt b + wt c := by
  by_contra h
  have single (p q r : P) (hp : p ≠ 0)
      (hw : wt p + wt q + wt r < 2) : q = 0 ∧ r = 0 := by
    have := wt_pos hp
    exact ⟨wt_eq_zero.mp (by omega), wt_eq_zero.mp (by omega)⟩
  rcases hn with ha | hb | hc
  · obtain ⟨rfl, rfl⟩ := single a b c ha (by omega)
    exact mul_ne_zero hA ha (by simpa using he)
  · obtain ⟨rfl, rfl⟩ := single b a c hb (by omega)
    exact mul_ne_zero hB hb (by simpa using he)
  · obtain ⟨rfl, rfl⟩ := single c a b hc (by omega)
    exact mul_ne_zero hC hc (by simpa using he)

/-- F equations at k+2 and k+3, with zero slices k and k+3. -/
theorem gap_three_forward (p q u v : P)
    (h₁ : u = q + s * v) (h₂ : t * p + q + v = 0)
    (hocc : 1 ≤ pairWt p q + pairWt u v) :
    4 ≤ pairWt p q + pairWt u v := by
  by_cases hu : u = 0
  · have hq : q = s * v := by simpa [hu, CharTwo.add_eq_zero] using h₁.symm
    have hv : v ≠ 0 := by
      intro hv
      have hp : p = 0 := (mul_eq_zero.mp (by simpa [hq, hv] using h₂)).resolve_left t_ne_zero
      simp [pairWt, hp, hq, hv, hu] at hocc
    have he : t * p = (1 + s) * v := by
      rw [hq] at h₂
      linear_combination (norm := (ring_nf <;> simp)) h₂
    have hp : p ≠ 0 := by
      intro hp
      exact mul_ne_zero one_add_s_ne_zero hv (by simpa [hp] using he.symm)
    have hw := two_le_wt_of_eval_one_zero hp (eval_one_zero_of_t_mul_eq he)
    have hvw := wt_pos hv
    simp only [pairWt, hu, wt_zero, hq, wt_s_mul]
    omega
  · have he : u.eval 1 = 0 := by
      have h₁e := congrArg (Polynomial.eval (1 : ZMod 2)) h₁
      have h₂e := congrArg (Polynomial.eval (1 : ZMod 2)) h₂
      simp [t, s] at h₁e h₂e
      exact h₁e.trans h₂e
    have huw := two_le_wt_of_eval_one_zero hu he
    have hrest := three_term_cost p q v t 1 1 t_ne_zero one_ne_zero one_ne_zero
      (by simpa using h₂) (by
        by_contra hn
        push_neg at hn
        exact hu (by simpa [hn.2.1, hn.2.2] using h₁))
    unfold pairWt
    omega

/-- B equations at k+2 and k+3, with zero slices k and k+3. -/
theorem gap_three_backward (p q u v : P)
    (h₁ : t * v = u + s * p) (h₂ : q = s * (u + p))
    (hocc : 1 ≤ pairWt p q + pairWt u v) :
    4 ≤ pairWt p q + pairWt u v := by
  by_cases hq : q = 0
  · have hup : u = p := by
      have : s * (u + p) = 0 := by simpa [hq] using h₂.symm
      exact CharTwo.add_eq_zero.mp (s_mul_eq_zero.mp this)
    have hp : p ≠ 0 := by
      intro hp
      have hv : v = 0 := (mul_eq_zero.mp (by simpa [hup, hp] using h₁)).resolve_left t_ne_zero
      simp [pairWt, hp, hup, hv, hq] at hocc
    have he : t * v = (1 + s) * p := by
      rw [hup] at h₁
      linear_combination (norm := (ring_nf <;> simp)) h₁
    have hv : v ≠ 0 := by
      intro hv
      exact mul_ne_zero one_add_s_ne_zero hp (by simpa [hv] using he.symm)
    have hw := two_le_wt_of_eval_one_zero hv (eval_one_zero_of_t_mul_eq he)
    have hpw := wt_pos hp
    simp only [pairWt, hq, wt_zero, hup]
    omega
  · have he : q.eval 1 = 0 := by
      have h₁e := congrArg (Polynomial.eval (1 : ZMod 2)) h₁
      have h₂e := congrArg (Polynomial.eval (1 : ZMod 2)) h₂
      simp [t, s] at h₁e h₂e
      exact h₂e.trans h₁e.symm
    have hqw := two_le_wt_of_eval_one_zero hq he
    have hrest := three_term_cost v u p t 1 s t_ne_zero one_ne_zero s_ne_zero
      (by linear_combination (norm := (ring_nf <;> simp)) h₁) (by
        by_contra hn
        push_neg at hn
        exact hq (by simpa [hn.2.1, hn.2.2] using h₂))
    unfold pairWt
    omega

/-- F: three occupied slices between zero endpoints cost at least four. -/
theorem gap_four_forward (p q u v h l : P)
    (h₁ : u = q + s * v) (h₂ : h = t * p + v + q + s * l)
    (h₃ : 0 = t * u + l + v)
    (hpq : 1 ≤ pairWt p q) (huv : 1 ≤ pairWt u v) (hhl : 1 ≤ pairWt h l) :
    4 ≤ pairWt p q + pairWt u v + pairWt h l := by
  by_contra hcost
  have wpq : pairWt p q = 1 := by omega
  have wuv : pairWt u v = 1 := by omega
  have whl : pairWt h l = 1 := by omega
  have hq : wt q = 1 := by
    have he : u + s * v = q := by linear_combination (norm := (ring_nf <;> simp)) h₁
    simpa only [he] using singleton_forward wuv
  have hp : p = 0 := wt_eq_zero.mp (by unfold pairWt at wpq; omega)
  rcases singleton_blocks wuv with ⟨wu, hv⟩ | ⟨hu, wv⟩
  · have hu : u ≠ 0 := by intro hz; simp [hz] at wu
    have hl : l = t * u := by
      rw [hv] at h₃
      linear_combination (norm := (ring_nf <;> simp)) h₃
    have hw := two_le_wt_t_mul hu
    unfold pairWt at whl
    rw [hl] at whl
    omega
  · have hl : l = v := by simpa [hu, CharTwo.add_eq_zero] using h₃.symm
    have hh : h = 0 := wt_eq_zero.mp (by unfold pairWt at whl; rw [hl] at whl; omega)
    have he : q = (1 + s) * v := by
      rw [hp, hh, hl] at h₂
      linear_combination (norm := (ring_nf <;> simp)) h₂
    have hv : v ≠ 0 := by intro hz; simp [hz] at wv
    have hw := two_le_wt_one_add_s_mul hv
    rw [← he] at hw
    omega

/-- B: three occupied slices between zero endpoints cost at least four. -/
theorem gap_four_backward (p q u v h l : P)
    (h₁ : t * v = u + s * p)
    (h₂ : t * l = h + s * u + s * p + q)
    (h₃ : v = s * (h + u))
    (hpq : 1 ≤ pairWt p q) (huv : 1 ≤ pairWt u v) (hhl : 1 ≤ pairWt h l) :
    4 ≤ pairWt p q + pairWt u v + pairWt h l := by
  by_contra hcost
  have wpq : pairWt p q = 1 := by omega
  have wuv : pairWt u v = 1 := by omega
  have whl : pairWt h l = 1 := by omega
  have hv : v = 0 := by
    by_contra hv
    have wv := wt_pos hv
    have hu : u = 0 := wt_eq_zero.mp (by unfold pairWt at wuv; omega)
    have he : t * v = s * p := by simpa [hu] using h₁
    have hw := two_le_wt_t_mul hv
    rw [he, wt_s_mul] at hw
    unfold pairWt at wpq
    omega
  have wu : wt u = 1 := by unfold pairWt at wuv; simpa [hv] using wuv
  have hh : h = u := by
    have hz : s * (h + u) = 0 := by simpa [hv] using h₃.symm
    exact CharTwo.add_eq_zero.mp (s_mul_eq_zero.mp hz)
  have hl : l = 0 := wt_eq_zero.mp (by unfold pairWt at whl; rw [hh] at whl; omega)
  have hsp : s * p = u := by
    rw [hv] at h₁
    linear_combination (norm := (ring_nf <;> simp)) h₁
  have wp : wt p = 1 := by
    have he := congrArg wt hsp
    simpa only [wt_s_mul, wu] using he
  have hq : q = 0 := wt_eq_zero.mp (by unfold pairWt at wpq; omega)
  have hz : s * u = 0 := by
    rw [hl, hh, hsp, hq] at h₂
    linear_combination (norm := (ring_nf <;> simp)) h₂
  have hu := s_mul_eq_zero.mp hz
  simp [hu] at wu

/-- F: four occupied slices following a zero cost at least five.
The equations are at k+2, k+3, k+4; no right zero is required. -/
theorem gap_five_forward (p q u v h l m n : P)
    (h₁ : u + s * v = q)
    (h₂ : h + s * l = t * p + v + q)
    (h₃ : m + s * n = t * u + l + v)
    (hpq : 1 ≤ pairWt p q) (huv : 1 ≤ pairWt u v)
    (hhl : 1 ≤ pairWt h l) (hmn : 1 ≤ pairWt m n) :
    5 ≤ pairWt p q + pairWt u v + pairWt h l + pairWt m n := by
  by_contra hcost
  have wpq : pairWt p q = 1 := by omega
  have wuv : pairWt u v = 1 := by omega
  have whl : pairWt h l = 1 := by omega
  have wmn : pairWt m n = 1 := by omega
  have wq : wt q = 1 := by simpa only [h₁] using singleton_forward wuv
  have hp : p = 0 := wt_eq_zero.mp (by unfold pairWt at wpq; omega)
  have hv : v = 0 := by
    rcases singleton_blocks wuv with ⟨_, hv⟩ | ⟨hu, wv⟩
    · exact hv
    · have hq : q = s * v := by simpa [hu] using h₁.symm
      have he : h + s * l = (1 + s) * v := by
        rw [hp, hq] at h₂
        linear_combination (norm := (ring_nf <;> simp)) h₂
      have hv : v ≠ 0 := by intro hz; simp [hz] at wv
      have hw := two_le_wt_one_add_s_mul hv
      have hs := singleton_forward whl
      rw [he] at hs
      omega
  have huq : u = q := by simpa [hv] using h₁
  have he : h + s * l = q := by simpa [hp, hv] using h₂
  have hs := singleton_forward wmn
  rcases singleton_blocks whl with ⟨_, hl⟩ | ⟨hh, wl⟩
  · have hq : q ≠ 0 := by intro hz; simp [hz] at wq
    have hw := two_le_wt_t_mul hq
    have hm : m + s * n = t * q := by simpa [huq, hl, hv] using h₃
    rw [hm] at hs
    omega
  · have hql : q = s * l := by simpa [hh] using he.symm
    have hm : m + s * n = (1 + X ^ 3 + X ^ 4) * l := by
      rw [huq, hql, hv] at h₃
      dsimp [t, s] at h₃ ⊢
      exact h₃.trans (by ring)
    have hw := wt_terminal wl
    rw [hm, hw] at hs
    omega

/-- B: four occupied slices preceding a zero cost at least five.
Arguments run in decreasing order R-1,...,R-4; equations are at R,R-1,R-2.
No left zero is required. -/
theorem gap_five_backward (p q u v h l m n : P)
    (h₁ : s * u + v = s * p)
    (h₂ : s * h + l = t * q + p + s * u)
    (h₃ : s * m + n = t * v + u + s * h)
    (hpq : 1 ≤ pairWt p q) (huv : 1 ≤ pairWt u v)
    (hhl : 1 ≤ pairWt h l) (hmn : 1 ≤ pairWt m n) :
    5 ≤ pairWt p q + pairWt u v + pairWt h l + pairWt m n := by
  by_contra hcost
  have wpq : pairWt p q = 1 := by omega
  have wuv : pairWt u v = 1 := by omega
  have whl : pairWt h l = 1 := by omega
  have wmn : pairWt m n = 1 := by omega
  have wp : wt p = 1 := by simpa only [h₁, wt_s_mul] using singleton_backward wuv
  have hq : q = 0 := wt_eq_zero.mp (by unfold pairWt at wpq; omega)
  have hu : u = 0 := by
    rcases singleton_blocks wuv with ⟨wu, hv⟩ | ⟨hu, _⟩
    · have hup : u = p := by
        apply mul_left_cancel₀ s_ne_zero
        simpa [hv] using h₁
      have he : s * h + l = (1 + s) * p := by
        rw [hq, hup] at h₂
        linear_combination (norm := (ring_nf <;> simp)) h₂
      have hp : p ≠ 0 := by intro hz; simp [hz] at wp
      have hw := two_le_wt_one_add_s_mul hp
      have hs := singleton_backward whl
      rw [he] at hs
      omega
    · exact hu
  have hvp : v = s * p := by simpa [hu] using h₁
  have he : s * h + l = p := by simpa [hq, hu] using h₂
  have hs := singleton_backward wmn
  rcases singleton_blocks whl with ⟨_, hl⟩ | ⟨hh, _⟩
  · have hph : s * h = p := by simpa [hl] using he
    have hm : s * m + n = (1 + X ^ 3 + X ^ 4) * p := by
      rw [hvp, hu, hph] at h₃
      dsimp [t, s] at h₃ ⊢
      exact h₃.trans (by ring)
    have hw := wt_terminal wp
    rw [hm, hw] at hs
    omega
  · have hp : p ≠ 0 := by intro hz; simp [hz] at wp
    have hv : s * p ≠ 0 := mul_ne_zero s_ne_zero hp
    have hw := two_le_wt_t_mul hv
    have hm : s * m + n = t * (s * p) := by simpa [hvp, hu, hh] using h₃
    rw [hm] at hs
    omega

/-- Arithmetic endpoint of the draft. The global counting layer must supply
these budgets; this theorem does not assert that arbitrary strips have them. -/
theorem fifteen_of_budgets (W E z G H K L : ℕ)
    (hweight : W + z = 19 + E)
    (hbranch : G ≤ E + 1)
    (hinterior : 2 * H + K + L ≤ E)
    (hspan : 6 * z ≤ 4 * G + 3 * H + 2 * K + L + 24) : 15 ≤ W := by
  omega

end
end QldpcVerification.Planar.StripLocal
