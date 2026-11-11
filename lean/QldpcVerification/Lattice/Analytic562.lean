import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! A symbolic shortest-vector bound for the lattice `281 ∣ 7 * u + 145 * v`.
The basis `(9, -14), (13, 11)` has determinant 281. Short vectors have
basis coefficients in `{-1, 0, 1}`, leaving nine explicit arithmetic cases. -/

namespace QldpcVerification.Lattice.Analytic562

theorem basis_det : (9 : ℤ) * 11 - 13 * (-14) = 281 := by
  rfl

/-- Recover integral basis coefficients from the divisibility witness. -/
theorem basis_coordinates {u v k : ℤ} (hk : 7 * u + 145 * v = 281 * k) :
    let a := 122 * k - 3 * u - 63 * v
    let b := 2 * k - v
    281 * a = 11 * u - 13 * v ∧
      281 * b = 14 * u + 9 * v ∧
      u = 9 * a + 13 * b ∧ v = -14 * a + 11 * b := by
  dsimp only
  constructor
  · nlinarith [hk]
  constructor
  · nlinarith [hk]
  constructor <;> nlinarith [hk]

/-- The two displayed vectors form an integral basis, including uniqueness. -/
theorem basis_iff (u v : ℤ) :
    (281 ∣ 7 * u + 145 * v) ↔
      ∃! p : ℤ × ℤ, u = 9 * p.1 + 13 * p.2 ∧ v = -14 * p.1 + 11 * p.2 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨ha, hb, hu, hv⟩ := basis_coordinates hk
    refine ⟨(122 * k - 3 * u - 63 * v, 2 * k - v), ⟨hu, hv⟩, ?_⟩
    intro p hp
    apply Prod.ext <;> dsimp only <;> nlinarith [hp.1, hp.2]
  · rintro ⟨p, hp, _⟩
    refine ⟨-7 * p.1 + 6 * p.2, ?_⟩
    rw [hp.1, hp.2]
    ring

/-- The inverse basis bounds force each coefficient of a short vector into `[-1, 1]`. -/
theorem coefficient_bounds {u v a b : ℤ}
    (ha : 281 * a = 11 * u - 13 * v)
    (hb : 281 * b = 14 * u + 9 * v)
    (hs : u.natAbs + v.natAbs ≤ 22) :
    (-1 ≤ a ∧ a ≤ 1) ∧ (-1 ≤ b ∧ b ≤ 1) := by
  have hu : -(u.natAbs : ℤ) ≤ u ∧ u ≤ (u.natAbs : ℤ) := by omega
  have hv : -(v.natAbs : ℤ) ≤ v ∧ v ≤ (v.natAbs : ℤ) := by omega
  have hu_nonneg : (0 : ℤ) ≤ u.natAbs := by omega
  have hv_nonneg : (0 : ℤ) ≤ v.natAbs := by omega
  have hs' : (u.natAbs : ℤ) + (v.natAbs : ℤ) ≤ 22 := by omega
  have ha_abs : -(13 * 22 : ℤ) ≤ 281 * a ∧ 281 * a ≤ 13 * 22 := by
    constructor <;> nlinarith
  have hb_abs : -(14 * 22 : ℤ) ≤ 281 * b ∧ 281 * b ≤ 14 * 22 := by
    constructor <;> nlinarith
  -- Both numerator bounds are strictly less than twice the determinant.
  have ha_small : (13 * 22 : ℤ) < 562 := by omega
  have hb_small : (14 * 22 : ℤ) < 562 := by omega
  omega

/-- Every nonzero vector in this lattice has L1 norm at least 23. -/
theorem norm_ge_23 {u v : ℤ} (hc : 281 ∣ 7 * u + 145 * v)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs := by
  by_contra h
  have hs : u.natAbs + v.natAbs ≤ 22 := by omega
  obtain ⟨k, hk⟩ := hc
  let a : ℤ := 122 * k - 3 * u - 63 * v
  let b : ℤ := 2 * k - v
  have hcoords : 281 * a = 11 * u - 13 * v ∧
      281 * b = 14 * u + 9 * v ∧
      u = 9 * a + 13 * b ∧ v = -14 * a + 11 * b :=
    basis_coordinates hk
  obtain ⟨ha, hb, hu, hv⟩ := hcoords
  obtain ⟨hab, hbb⟩ := coefficient_bounds ha hb hs
  have hac : a = 0 ∨ a = 1 ∨ a = -1 := by omega
  have hbc : b = 0 ∨ b = 1 ∨ b = -1 := by omega
  rcases hac with ha0 | ha1 | han
  · rcases hbc with hb0 | hb1 | hbn
    · -- (0, 0): the zero vector, excluded by `hn`.
      have hz : u = 0 ∧ v = 0 := by omega
      omega
    · -- (0, 1): q has norm 24.
      have hnorm : u.natAbs + v.natAbs = 24 := by omega
      omega
    · -- (0, -1): -q has norm 24.
      have hnorm : u.natAbs + v.natAbs = 24 := by omega
      omega
  · rcases hbc with hb0 | hb1 | hbn
    · -- (1, 0): p has norm 23.
      have hnorm : u.natAbs + v.natAbs = 23 := by omega
      omega
    · -- (1, 1): p + q = (22, -3) has norm 25.
      have hnorm : u.natAbs + v.natAbs = 25 := by omega
      omega
    · -- (1, -1): p - q = (-4, -25) has norm 29.
      have hnorm : u.natAbs + v.natAbs = 29 := by omega
      omega
  · rcases hbc with hb0 | hb1 | hbn
    · -- (-1, 0): -p has norm 23.
      have hnorm : u.natAbs + v.natAbs = 23 := by omega
      omega
    · -- (-1, 1): -p + q = (4, 25) has norm 29.
      have hnorm : u.natAbs + v.natAbs = 29 := by omega
      omega
    · -- (-1, -1): -p - q = (-22, 3) has norm 25.
      have hnorm : u.natAbs + v.natAbs = 25 := by omega
      omega

theorem norm_ge_23_of_cast {u v : ℤ}
    (hc : (7 : ZMod 281) * (u : ZMod 281) + 145 * (v : ZMod 281) = 0)
    (hn : u ≠ 0 ∨ v ≠ 0) : 23 ≤ u.natAbs + v.natAbs := by
  apply norm_ge_23 (hn := hn)
  have h : ((7 * u + 145 * v : ℤ) : ZMod 281) = 0 := by simpa using hc
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

/-- The basis vector p attains the lower bound (with quotient -7). -/
theorem shortest_vector_witness :
    (281 ∣ 7 * (9 : ℤ) + 145 * (-14)) ∧
      (9 : ℤ).natAbs + (-14 : ℤ).natAbs = 23 := by
  exact ⟨⟨-7, rfl⟩, rfl⟩

end QldpcVerification.Lattice.Analytic562
