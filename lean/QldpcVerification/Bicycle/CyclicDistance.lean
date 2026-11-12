import QldpcVerification.Bicycle.ShortestVector
import QldpcVerification.Bicycle.ComponentParameters
import QldpcVerification.Bicycle.GcdComponents

/-! Exact shortest-relation distances without a connectivity hypothesis. -/

namespace QldpcVerification.Bicycle.Connected

open Module

theorem relation_scaled_iff (c l a b : ℕ) [NeZero c] (u v : ℤ) :
    ((c * a : ℕ) : ZMod (c * l)) * (u : ZMod (c * l)) +
      ((c * b : ℕ) : ZMod (c * l)) * (v : ZMod (c * l)) = 0 ↔
    (a : ZMod l) * (u : ZMod l) + (b : ZMod l) * (v : ZMod l) = 0 := by
  have hc : (c : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
  have hbig : (((c * l : ℕ) : ℤ) ∣ ((c * a : ℕ) : ℤ) * u +
      ((c * b : ℕ) : ℤ) * v) ↔ ((l : ℤ) ∣ (a : ℤ) * u + (b : ℤ) * v) := by
    push_cast
    rw [show (c : ℤ) * a * u + (c : ℤ) * b * v =
      (c : ℤ) * ((a : ℤ) * u + (b : ℤ) * v) by ring]
    exact Int.mul_dvd_mul_iff_left hc
  have hh := ((ZMod.intCast_zmod_eq_zero_iff_dvd
    (((c * a : ℕ) : ℤ) * u + ((c * b : ℕ) : ℤ) * v) (c * l)).trans hbig).trans
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) * u + (b : ℤ) * v) l).symm
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hh

theorem minimumNorm_scaled (c l a b : ℕ) [NeZero c] [NeZero l] :
    minimumNorm (m := c * l) (c * a) (c * b) = minimumNorm (m := l) a b := by
  apply le_antisymm
  · obtain ⟨u, v, hn, hr, hw⟩ := minimumNorm_attained (m := l) a b
    rw [← hw]
    apply minimumNorm_lower _ _ u v hn
    exact (relation_scaled_iff c l a b u v).mpr hr
  · obtain ⟨u, v, hn, hr, hw⟩ := minimumNorm_attained (m := c * l) (c * a) (c * b)
    rw [← hw]
    apply minimumNorm_lower _ _ u v hn
    exact (relation_scaled_iff c l a b u v).mp hr

theorem Match.parameters_factored {c l a b n mX mZ : ℕ} [NeZero c] [NeZero l]
    (M : Match (c * l) (c * a) (c * b) n mX mZ)
    (hc : Nat.gcd (Nat.gcd a b) l = 1) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = c * 2) ∧
      M.code.DistX (minimumNorm (m := c * l) (c * a) (c * b)) ∧
      M.code.DistZ (minimumNorm (m := c * l) (c * a) (c * b)) := by
  have hsmall := (canonicalMatch l a b).parameters_minimum hc
  refine ⟨Decomposition.MatrixMatch.encoded_qubits M hc, ?_, ?_⟩
  · rw [minimumNorm_scaled c l a b]
    exact (Decomposition.matrix_distanceX_iff M (canonicalMatch l a b) _).mpr hsmall.2.1
  · rw [minimumNorm_scaled c l a b]
    exact (Decomposition.matrix_distanceZ_iff M (canonicalMatch l a b) _).mpr hsmall.2.2

/-- Every positive cyclic binomial code has distance equal to its shortest period relation. -/
theorem Match.parameters_all {m s t n mX mZ : ℕ} [NeZero m]
    (M : Match m s t n mX mZ) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab =
      Decomposition.count m s t * 2) ∧
      M.code.DistX (minimumNorm (m := m) s t) ∧
      M.code.DistZ (minimumNorm (m := m) s t) := by
  let c := Decomposition.count m s t
  let l := m / c
  let a := s / c
  let b := t / c
  have hc0 : 0 < c := Decomposition.count_pos m s t
  have hl0 : 0 < l := Decomposition.quotient_pos m s t
  letI : NeZero c := ⟨Nat.ne_of_gt hc0⟩
  letI : NeZero l := ⟨Nat.ne_of_gt hl0⟩
  have hc : Nat.gcd (Nat.gcd a b) l = 1 := Decomposition.reduced_coprime m s t
  obtain ⟨hm, hs, ht⟩ := Decomposition.factors m s t
  change m = c * l at hm
  change s = c * a at hs
  change t = c * b at ht
  have hgen : ∀ (m s t : ℕ) [NeZero m],
      m = c * l → s = c * a → t = c * b →
      ∀ M : Match m s t n mX mZ,
      (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = c * 2) ∧
        M.code.DistX (minimumNorm (m := m) s t) ∧
        M.code.DistZ (minimumNorm (m := m) s t) := by
    intro m s t _ hm hs ht M
    subst m
    subst s
    subst t
    exact M.parameters_factored hc
  exact hgen m s t hm hs ht M

theorem Match.rankX_all {m s t n mX mZ : ℕ} [NeZero m]
    (M : Match m s t n mX mZ) :
    finrank (ZMod 2) M.code.xStab = m - Decomposition.count m s t := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.xStab =
      Submodule.span (ZMod 2) (Set.range (H s t)) :=
    rowspace_pull M.qubits M.HX (H s t) M.xRow M.x_surjective M.x_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.xStab, h]
  exact (Decomposition.gcd_ranks m s t).1

theorem Match.rankZ_all {m s t n mX mZ : ℕ} [NeZero m]
    (M : Match m s t n mX mZ) :
    finrank (ZMod 2) M.code.zStab = m - Decomposition.count m s t := by
  have h : Submodule.map (pull M.qubits).toLinearMap M.code.zStab =
      Submodule.span (ZMod 2) (Set.range (F s t)) :=
    rowspace_pull M.qubits M.HZ (F s t) M.zRow M.z_surjective M.z_rows
  rw [← (pull M.qubits).finrank_map_eq M.code.zStab, h]
  exact (Decomposition.gcd_ranks m s t).2

end QldpcVerification.Bicycle.Connected
