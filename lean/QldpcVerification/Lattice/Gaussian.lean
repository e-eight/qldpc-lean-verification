import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Symbolic L1 minima for coprime rotated square period lattices and their covers. -/

namespace QldpcVerification.Lattice.Gaussian

/-- Integer combinations of two perpendicular equal-length vectors have no smaller L1 norm. -/
theorem rotated_norm_ge (a b i j : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hn : i ≠ 0 ∨ j ≠ 0) :
    a + b ≤ |b * i + a * j| + |-a * i + b * j| := by
  by_cases hi : i = 0
  · have hj : 1 ≤ |j| := by
      have hj0 : j ≠ 0 := hn.resolve_left (by simpa [hi])
      have := abs_pos.mpr hj0
      omega
    simp only [hi, mul_zero, zero_add, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith
  by_cases hj : j = 0
  · have hi' : 1 ≤ |i| := by have := abs_pos.mpr hi; omega
    simp only [hj, mul_zero, add_zero, abs_mul, abs_neg,
      abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith
  have hi2 : 1 ≤ i ^ 2 := by nlinarith [sq_pos_of_ne_zero hi]
  have hj2 : 1 ≤ j ^ 2 := by nlinarith [sq_pos_of_ne_zero hj]
  have hscale : 2 * (a ^ 2 + b ^ 2) ≤
      (a ^ 2 + b ^ 2) * (i ^ 2 + j ^ 2) := by
    nlinarith [mul_nonneg (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
      (show 0 ≤ i ^ 2 + j ^ 2 - 2 by omega)]
  have hid : (b * i + a * j) ^ 2 + (-a * i + b * j) ^ 2 =
      (a ^ 2 + b ^ 2) * (i ^ 2 + j ^ 2) := by ring
  have hp := mul_nonneg (abs_nonneg (b * i + a * j))
    (abs_nonneg (-a * i + b * j))
  have hsq1 := sq_abs (b * i + a * j)
  have hsq2 := sq_abs (-a * i + b * j)
  nlinarith [sq_nonneg (a - b), abs_nonneg (b * i + a * j),
    abs_nonneg (-a * i + b * j)]

/-- Bézout coefficients recover integral coordinates without modular inverses. -/
theorem coordinates {a b p q u v k : ℤ}
    (hbez : a * p + b * q = 1) (hpos : 0 < a ^ 2 + b ^ 2)
    (hrel : a * u + b * v = (a ^ 2 + b ^ 2) * k) :
    ∃ i j : ℤ, u = b * i + a * j ∧ v = -a * i + b * j := by
  let i := p * (b * k - v) + q * (u - a * k)
  have hi : (a ^ 2 + b ^ 2) * i = b * u - a * v := by
    dsimp [i]
    linear_combination (q * a - p * b) * hrel +
      (b * u - a * v) * hbez
  refine ⟨i, k, ?_, ?_⟩
  · apply mul_left_cancel₀ (ne_of_gt hpos)
    linear_combination a * hrel - b * hi
  · apply mul_left_cancel₀ (ne_of_gt hpos)
    linear_combination a * hi + b * hrel

/-- Every nonzero relation modulo a positive multiple of a²+b² has norm at least a+b. -/
theorem norm_ge (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hab : Nat.Coprime a b)
    (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hrel : (h * (a ^ 2 + b ^ 2) : ℤ) ∣ (a : ℤ) * u + (b : ℤ) * v) :
    a + b ≤ u.natAbs + v.natAbs := by
  obtain ⟨k, hk⟩ := hrel
  have hbez : (a : ℤ) * Int.gcdA a b + (b : ℤ) * Int.gcdB a b = 1 := by
    have hg := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
    simpa [hab.gcd_eq_one] using hg.symm
  have hpos : (0 : ℤ) < (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by
    have ha' : (0 : ℤ) < a := by exact_mod_cast ha
    nlinarith [sq_nonneg (b : ℤ)]
  have hk' : (a : ℤ) * u + (b : ℤ) * v =
      ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) * ((h : ℤ) * k) := by nlinarith [hk]
  obtain ⟨i, j, hu, hv⟩ := coordinates hbez hpos hk'
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra hzero
    push Not at hzero
    simp [hzero.1, hzero.2] at hu hv
    exact hn.elim (fun h => h hu) (fun h => h hv)
  have hl := rotated_norm_ge (a : ℤ) (b : ℤ) i j (by positivity) (by positivity) hij
  rw [← hu, ← hv] at hl
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hl
  exact_mod_cast hl

theorem norm_ge_of_cast (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hab : Nat.Coprime a b) (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hrel : (a : ZMod (h * (a ^ 2 + b ^ 2))) * (u : ZMod (h * (a ^ 2 + b ^ 2))) +
      (b : ZMod (h * (a ^ 2 + b ^ 2))) * (v : ZMod (h * (a ^ 2 + b ^ 2))) = 0) :
    a + b ≤ u.natAbs + v.natAbs := by
  apply norm_ge a b h ha hh hab u v hn
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hrel

theorem minimizing_pair (a b h : ℕ) (ha : 0 < a) :
    ((b : ℤ) ≠ 0 ∨ -(a : ℤ) ≠ 0) ∧
      (a : ZMod (h * (a ^ 2 + b ^ 2))) * ((b : ℤ) : ZMod (h * (a ^ 2 + b ^ 2))) +
        (b : ZMod (h * (a ^ 2 + b ^ 2))) * ((-(a : ℤ)) : ZMod (h * (a ^ 2 + b ^ 2))) = 0 ∧
      (b : ℤ).natAbs + (-(a : ℤ)).natAbs = a + b := by
  refine ⟨Or.inr (by omega), ?_, ?_⟩
  · push_cast
    ring
  · simp [Nat.add_comm]

end QldpcVerification.Lattice.Gaussian
