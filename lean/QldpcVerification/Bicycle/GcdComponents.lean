import QldpcVerification.Bicycle.ComponentBounds

/-! The common gcd determines the component count and the reduced connected parameters. -/

namespace QldpcVerification.Bicycle.Decomposition

open Matrix Module

def count (m s t : ℕ) := Nat.gcd (Nat.gcd s t) m

theorem count_pos (m s t : ℕ) [NeZero m] : 0 < count m s t :=
  Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne m))

theorem count_dvd (m s t : ℕ) : count m s t ∣ m ∧ count m s t ∣ s ∧ count m s t ∣ t := by
  exact ⟨Nat.gcd_dvd_right _ _,
    Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _),
    Nat.dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)⟩

theorem quotient_pos (m s t : ℕ) [NeZero m] : 0 < m / count m s t := by
  exact Nat.div_pos (Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne m))) (count_pos m s t)

theorem factors (m s t : ℕ) :
    m = count m s t * (m / count m s t) ∧
      s = count m s t * (s / count m s t) ∧ t = count m s t * (t / count m s t) := by
  obtain ⟨hm, hs, ht⟩ := count_dvd m s t
  exact ⟨(Nat.mul_div_cancel' hm).symm, (Nat.mul_div_cancel' hs).symm, (Nat.mul_div_cancel' ht).symm⟩

theorem reduced_coprime (m s t : ℕ) [NeZero m] :
    Nat.gcd (Nat.gcd (s / count m s t) (t / count m s t)) (m / count m s t) = 1 := by
  obtain ⟨hm, hs, ht⟩ := count_dvd m s t
  have hgc : count m s t ∣ Nat.gcd s t := Nat.gcd_dvd_left _ _
  rw [Nat.gcd_div hs ht, Nat.gcd_div hgc hm]
  exact Nat.div_self (count_pos m s t)

theorem ranks_of_factorization (m s t c l a b : ℕ) [NeZero m] [NeZero c] [NeZero l]
    (hm : m = c * l) (hs : s = c * a) (ht : t = c * b)
    (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.H (m := m) s t))) = m - c ∧
      finrank (ZMod 2) (Connected.boundaries (m := m) s t) = m - c := by
  subst m; subst s; subst t
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using ranks c l a b hc

theorem gcd_ranks (m s t : ℕ) [NeZero m] :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.H (m := m) s t))) = m - count m s t ∧
      finrank (ZMod 2) (Connected.boundaries (m := m) s t) = m - count m s t := by
  let c := count m s t
  let l := m / c
  letI : NeZero c := ⟨Nat.ne_of_gt (count_pos m s t)⟩
  letI : NeZero l := ⟨Nat.ne_of_gt (quotient_pos m s t)⟩
  obtain ⟨hm, hs, ht⟩ := factors m s t
  exact ranks_of_factorization m s t c l (s / c) (t / c) hm hs ht (reduced_coprime m s t)

theorem gcd_encoded_qubits (m s t : ℕ) [NeZero m] :
    (m + m) - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (Connected.H (m := m) s t))) -
      finrank (ZMod 2) (Connected.boundaries (m := m) s t) = count m s t * 2 := by
  obtain ⟨hx, hz⟩ := gcd_ranks m s t
  rw [hx, hz]
  have hc : count m s t ≤ m := Nat.gcd_le_right _ (Nat.pos_of_ne_zero (NeZero.ne m))
  omega

noncomputable def coverage_of_factorization (m s t c l a b : ℕ) [NeZero m] [NeZero c] [NeZero l]
    (hm : m = c * l) (hs : s = c * a) (ht : t = c * b)
    (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    CoverageCertificate (Connected.cycles (m := m) s t) (Connected.boundaries s t) (c * 2) := by
  subst m; subst s; subst t
  exact coverage c l a b hc

noncomputable def gcd_coverage (m s t : ℕ) [NeZero m] :
    CoverageCertificate (Connected.cycles (m := m) s t) (Connected.boundaries s t) (count m s t * 2) := by
  let c := count m s t
  let l := m / c
  let a := s / c
  let b := t / c
  letI : NeZero c := ⟨Nat.ne_of_gt (count_pos m s t)⟩
  letI : NeZero l := ⟨Nat.ne_of_gt (quotient_pos m s t)⟩
  obtain ⟨hm, hs, ht⟩ := factors m s t
  exact coverage_of_factorization m s t c l a b hm hs ht (reduced_coprime m s t)

end QldpcVerification.Bicycle.Decomposition
