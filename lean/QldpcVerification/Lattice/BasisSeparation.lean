import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Analytic separation for a normalized cyclic lattice from two integer basis
vectors. The inverse-coordinate inequalities derive the nine possible short
coefficient pairs; no finite lattice window is enumerated. -/

namespace QldpcVerification.Lattice.BasisSeparation

structure BasisData (m a D : ℕ) where
  p₁ : ℤ
  p₂ : ℤ
  q₁ : ℤ
  q₂ : ℤ
  pPeriod : ℤ
  qPeriod : ℤ
  p_relation : p₁ + (a : ℤ) * p₂ = (m : ℤ) * pPeriod
  q_relation : q₁ + (a : ℤ) * q₂ = (m : ℤ) * qPeriod
  quotient_det : pPeriod * q₂ - qPeriod * p₂ = 1
  p_margin : max p₁.natAbs p₂.natAbs * (D - 1) < 2 * m
  q_margin : max q₁.natAbs q₂.natAbs * (D - 1) < 2 * m
  p_norm : D ≤ p₁.natAbs + p₂.natAbs
  q_norm : D ≤ q₁.natAbs + q₂.natAbs
  add_norm : D ≤ (p₁ + q₁).natAbs + (p₂ + q₂).natAbs
  sub_norm : D ≤ (p₁ - q₁).natAbs + (p₂ - q₂).natAbs

namespace BasisData

variable {m a D : ℕ} (B : BasisData m a D)

theorem determinant : B.p₁ * B.q₂ - B.q₁ * B.p₂ = (m : ℤ) := by
  linear_combination B.q₂ * B.p_relation - B.p₂ * B.q_relation +
    (m : ℤ) * B.quotient_det

theorem coordinates (u v k : ℤ) (hk : u + (a : ℤ) * v = (m : ℤ) * k) :
    ∃ i j : ℤ, u = B.p₁ * i + B.q₁ * j ∧ v = B.p₂ * i + B.q₂ * j ∧
      (m : ℤ) * i = B.q₂ * u - B.q₁ * v ∧
      (m : ℤ) * j = -B.p₂ * u + B.p₁ * v := by
  let i := B.q₂ * k - B.qPeriod * v
  let j := B.pPeriod * v - B.p₂ * k
  have hc : B.q₁ * B.pPeriod - B.p₁ * B.qPeriod = -(a : ℤ) := by
    linear_combination B.pPeriod * B.q_relation - B.qPeriod * B.p_relation -
      (a : ℤ) * B.quotient_det
  have hu : u = B.p₁ * i + B.q₁ * j := by
    dsimp [i, j]
    linear_combination hk - k * B.determinant - v * hc
  have hv : v = B.p₂ * i + B.q₂ * j := by
    dsimp [i, j]
    linear_combination -v * B.quotient_det
  refine ⟨i, j, hu, hv, ?_, ?_⟩
  · linear_combination -i * B.determinant - B.q₂ * hu + B.q₁ * hv
  · linear_combination -j * B.determinant + B.p₂ * hu - B.p₁ * hv

theorem basis_iff (hm : 0 < m) (u v : ℤ) :
    ((m : ℤ) ∣ u + (a : ℤ) * v) ↔
      ∃! c : ℤ × ℤ, u = B.p₁ * c.1 + B.q₁ * c.2 ∧
        v = B.p₂ * c.1 + B.q₂ * c.2 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨i, j, hu, hv, hi, hj⟩ := B.coordinates u v k hk
    refine ⟨(i, j), ⟨hu, hv⟩, ?_⟩
    intro c hc
    apply Prod.ext
    · have he : (m : ℤ) * c.1 = B.q₂ * u - B.q₁ * v := by
        linear_combination -c.1 * B.determinant - B.q₂ * hc.1 + B.q₁ * hc.2
      exact mul_left_cancel₀ hm0 (he.trans hi.symm)
    · have he : (m : ℤ) * c.2 = -B.p₂ * u + B.p₁ * v := by
        linear_combination -c.2 * B.determinant + B.p₂ * hc.1 - B.p₁ * hc.2
      exact mul_left_cancel₀ hm0 (he.trans hj.symm)
  · rintro ⟨c, hc, _⟩
    refine ⟨B.pPeriod * c.1 + B.qPeriod * c.2, ?_⟩
    rw [hc.1, hc.2]
    linear_combination c.1 * B.p_relation + c.2 * B.q_relation

private theorem difference_bound (x y u v : ℤ) :
    (x * u - y * v).natAbs ≤ max x.natAbs y.natAbs * (u.natAbs + v.natAbs) := by
  calc
    (x * u - y * v).natAbs ≤ (x * u).natAbs + (y * v).natAbs :=
      Int.natAbs_sub_le _ _
    _ = x.natAbs * u.natAbs + y.natAbs * v.natAbs := by simp [Int.natAbs_mul]
    _ ≤ max x.natAbs y.natAbs * (u.natAbs + v.natAbs) := by
      have h₁ := Nat.mul_le_mul_right u.natAbs (le_max_left x.natAbs y.natAbs)
      have h₂ := Nat.mul_le_mul_right v.natAbs (le_max_right x.natAbs y.natAbs)
      nlinarith

theorem short_coordinates (hm : 0 < m) (u v i j : ℤ)
    (hi : (m : ℤ) * i = B.q₂ * u - B.q₁ * v)
    (hj : (m : ℤ) * j = -B.p₂ * u + B.p₁ * v)
    (hw : u.natAbs + v.natAbs ≤ D - 1) :
    (i = 0 ∨ i = 1 ∨ i = -1) ∧ (j = 0 ∨ j = 1 ∨ j = -1) := by
  have hi' : m * i.natAbs < m * 2 := by
    calc
      m * i.natAbs = ((m : ℤ) * i).natAbs := by simp [Int.natAbs_mul]
      _ = (B.q₂ * u - B.q₁ * v).natAbs := congrArg Int.natAbs hi
      _ ≤ max B.q₂.natAbs B.q₁.natAbs * (u.natAbs + v.natAbs) :=
        difference_bound _ _ _ _
      _ ≤ max B.q₂.natAbs B.q₁.natAbs * (D - 1) := Nat.mul_le_mul_left _ hw
      _ < m * 2 := by simpa [max_comm, Nat.mul_comm] using B.q_margin
  have hj' : m * j.natAbs < m * 2 := by
    calc
      m * j.natAbs = ((m : ℤ) * j).natAbs := by simp [Int.natAbs_mul]
      _ = (B.p₁ * v - B.p₂ * u).natAbs := by
        rw [hj]
        congr 1
        ring
      _ ≤ max B.p₁.natAbs B.p₂.natAbs * (v.natAbs + u.natAbs) :=
        difference_bound _ _ _ _
      _ ≤ max B.p₁.natAbs B.p₂.natAbs * (D - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      _ < m * 2 := by simpa [Nat.mul_comm] using B.p_margin
  have hib : i.natAbs < 2 := (Nat.mul_lt_mul_left hm).mp hi'
  have hjb : j.natAbs < 2 := (Nat.mul_lt_mul_left hm).mp hj'
  omega

include B in
theorem norm_ge (hm : 0 < m) (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hrel : (m : ℤ) ∣ u + (a : ℤ) * v) : D ≤ u.natAbs + v.natAbs := by
  by_contra hsmall
  have hw : u.natAbs + v.natAbs ≤ D - 1 := by omega
  obtain ⟨k, hk⟩ := hrel
  obtain ⟨i, j, hu, hv, hi, hj⟩ := B.coordinates u v k hk
  obtain ⟨hic, hjc⟩ := B.short_coordinates hm u v i j hi hj hw
  rw [hu, hv] at hsmall
  rcases hic with hi0 | hi1 | hin
  · rcases hjc with hj0 | hj1 | hjn
    · simp [hi0, hj0] at hu hv
      exact hn.elim (fun h => h hu) (fun h => h hv)
    · exact hsmall (by simpa [hi0, hj1] using B.q_norm)
    · exact hsmall (by simpa [hi0, hjn] using B.q_norm)
  · rcases hjc with hj0 | hj1 | hjn
    · exact hsmall (by simpa [hi1, hj0] using B.p_norm)
    · exact hsmall (by simpa [hi1, hj1] using B.add_norm)
    · exact hsmall (by simpa [hi1, hjn, sub_eq_add_neg] using B.sub_norm)
  · rcases hjc with hj0 | hj1 | hjn
    · exact hsmall (by simpa [hin, hj0] using B.p_norm)
    · have h₁ : -B.p₁ + B.q₁ = -(B.p₁ - B.q₁) := by ring
      have h₂ : -B.p₂ + B.q₂ = -(B.p₂ - B.q₂) := by ring
      exact hsmall (by simpa only [hin, hj1, mul_neg_one, mul_one, h₁, h₂,
        Int.natAbs_neg] using B.sub_norm)
    · have h₁ : -B.p₁ + -B.q₁ = -(B.p₁ + B.q₁) := by ring
      have h₂ : -B.p₂ + -B.q₂ = -(B.p₂ + B.q₂) := by ring
      exact hsmall (by simpa only [hin, hjn, mul_neg_one, h₁, h₂,
        Int.natAbs_neg] using B.add_norm)

include B in
theorem bound (hm : 0 < m) (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0) :
    D ≤ u.natAbs + v.natAbs := by
  apply B.norm_ge hm u v hn
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa using hc

end BasisData
end QldpcVerification.Lattice.BasisSeparation
