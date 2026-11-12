import QldpcVerification.Planar.BulkExactness
import QldpcVerification.Planar.ChargeAlgebra

/-!
# Two empty strips force zero low charge

Symbolic polynomial truncation for Proposition 8 of `analytical/charge722/DRAFT.tex`.
The generic result works over any commutative semiring and any ring homomorphism
annihilating the two generators. No enumeration of physical words is involved.
The square-support hypotheses are unnecessary: only tested rows below the cut
are used. The column statement uses swapped polynomials and the transported
residue, so it does not assume an X/Z symmetry of the physical code.

Replay and axiom checking belong to the orchestrator's capped runner.
-/

namespace QldpcVerification.Planar.CutCharge

open Polynomial

noncomputable section

section Generic

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Retain exactly the outer-variable rows strictly below the cut. -/
def below (k : ℕ) (p : R[X]) : R[X] :=
  ∑ i ∈ Finset.range k, monomial i (p.coeff i)

@[simp] theorem coeff_below (k : ℕ) (p : R[X]) (i : ℕ) :
    (below k p).coeff i = if i < k then p.coeff i else 0 := by
  classical
  simp [below, finsetSum_coeff, coeff_monomial, eq_comm]

/-- Multiplication cannot bring discarded nonnegative exponents below the cut. -/
theorem coeff_mul_below (a p : R[X]) {k i : ℕ} (hi : i < k) :
    (a * below k p).coeff i = (a * p).coeff i := by
  classical
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = i := Finset.mem_antidiagonal.mp hij
  rw [coeff_below, if_pos (show ij.2 < k by omega)]

/-- The two empty last retained rows lower the support by two, including k = 2. -/
theorem coeff_below_gap (p : R[X]) {k j : ℕ} (hk : 2 ≤ k)
    (h₀ : p.coeff (k - 2) = 0) (h₁ : p.coeff (k - 1) = 0)
    (hj : k - 2 ≤ j) : (below k p).coeff j = 0 := by
  rw [coeff_below]
  split_ifs with hjk
  · have he : j = k - 2 ∨ j = k - 1 := by omega
    rcases he with rfl | rfl
    · exact h₀
    · exact h₁
  · rfl

/-- A quadratic generator times the gapped truncation has no rows at or above k. -/
theorem coeff_mul_below_gap (a p : R[X]) (ha : a.natDegree ≤ 2)
    {k i : ℕ} (hk : 2 ≤ k) (hi : k ≤ i)
    (h₀ : p.coeff (k - 2) = 0) (h₁ : p.coeff (k - 1) = 0) :
    (a * below k p).coeff i = 0 := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hsum : ij.1 + ij.2 = i := Finset.mem_antidiagonal.mp hij
  by_cases ha₂ : ij.1 ≤ 2
  · rw [coeff_below_gap p hk h₀ h₁ (show k - 2 ≤ ij.2 by omega), mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (show a.natDegree < ij.1 by omega), zero_mul]

/-- Exact cut identity in the presence of a two-row gap: the truncated full
syndrome is precisely the original syndrome's first two rows. -/
theorem cut_syndrome_eq_low (a b u v : R[X])
    (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2)
    {k : ℕ} (hk : 2 ≤ k)
    (hcycle : ∀ i, 2 ≤ i → i < k → (a * u + b * v).coeff i = 0)
    (hu₀ : u.coeff (k - 2) = 0) (hu₁ : u.coeff (k - 1) = 0)
    (hv₀ : v.coeff (k - 2) = 0) (hv₁ : v.coeff (k - 1) = 0) :
    a * below k u + b * below k v = below 2 (a * u + b * v) := by
  ext i
  rw [coeff_add, coeff_below]
  by_cases hik : i < k
  · rw [coeff_mul_below a u hik, coeff_mul_below b v hik, ← coeff_add]
    split_ifs with hi₂
    · rfl
    · exact hcycle i (by omega) hik
  · rw [coeff_mul_below_gap a u ha hk (by omega) hu₀ hu₁,
      coeff_mul_below_gap b v hb hk (by omega) hv₀ hv₁,
      if_neg (show ¬ i < 2 by omega), zero_add]

/-- Reusable quadratic cut-gap lemma for either coordinate orientation. -/
theorem cut_gap (ρ : R[X] →+* S) (a b u v : R[X])
    (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2)
    (hρa : ρ a = 0) (hρb : ρ b = 0)
    {k : ℕ} (hk : 2 ≤ k)
    (hcycle : ∀ i, 2 ≤ i → i < k → (a * u + b * v).coeff i = 0)
    (hu₀ : u.coeff (k - 2) = 0) (hu₁ : u.coeff (k - 1) = 0)
    (hv₀ : v.coeff (k - 2) = 0) (hv₁ : v.coeff (k - 1) = 0) :
    ρ (below 2 (a * u + b * v)) = 0 := by
  rw [← cut_syndrome_eq_low a b u v ha hb hk hcycle hu₀ hu₁ hv₀ hv₁]
  simp only [map_add, map_mul, hρa, hρb, zero_mul, zero_add]

end Generic

open BulkExactness

/-- Evaluate inner Y at y, then outer X at x, in the actual quotient algebra. -/
def residue : Bivariate →+* ChargeAlgebra.A :=
  eval₂RingHom
    (eval₂RingHom (algebraMap (ZMod 2) ChargeAlgebra.A) ChargeAlgebra.y)
    ChargeAlgebra.x

@[simp] theorem residue_f : residue f = 0 := by
  simp only [residue, f, quadratic, Y, coe_eval₂RingHom,
    eval₂_add, eval₂_pow, eval₂_C, eval₂_X]
  calc
    ChargeAlgebra.x ^ 2 + ChargeAlgebra.x + ChargeAlgebra.y ^ 2 =
        ChargeAlgebra.x + ChargeAlgebra.x ^ 2 + ChargeAlgebra.y ^ 2 := by ring
    _ = 0 := ChargeAlgebra.x_relation

@[simp] theorem residue_g : residue g = 0 := by
  simp only [residue, g, companion, BulkExactness.t, Y, coe_eval₂RingHom,
    eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X, eval₂_one]
  calc
    (ChargeAlgebra.y + ChargeAlgebra.y ^ 2) * ChargeAlgebra.x ^ 2 + 1 =
        1 + ChargeAlgebra.x ^ 2 * ChargeAlgebra.y +
          ChargeAlgebra.x ^ 2 * ChargeAlgebra.y ^ 2 := by ring
    _ = 0 := ChargeAlgebra.g_relation

/-- Every full polynomial syndrome has zero total residue. -/
theorem residue_syndrome (u v : Bivariate) : residue (g * u + f * v) = 0 := by
  simp only [map_add, map_mul, residue_g, residue_f, zero_mul, zero_add]

/-- Low-row charge, without any cycle or support assumption in its definition. -/
def lowCharge (u v : Bivariate) : ChargeAlgebra.A :=
  residue (below 2 (g * u + f * v))

theorem g_natDegree_le_two : g.natDegree ≤ 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have hi₀ : i ≠ 0 := by omega
  have hi₂ : 2 ≠ i := by omega
  simp [g, companion, coeff_C_mul, coeff_X_pow, coeff_one, hi₀, hi₂, Ne.symm hi₂]

/-- The charge9 row cut lemma, valid at both endpoint cuts 2 and 19.
In particular it applies to u,v in `BulkExactness.InSquare 18`. -/
theorem row_cut_gap (u v : Bivariate) {k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ 19)
    (hcycle : ∀ i, 2 ≤ i → i ≤ 18 → (g * u + f * v).coeff i = 0)
    (hu₀ : u.coeff (k - 2) = 0) (hu₁ : u.coeff (k - 1) = 0)
    (hv₀ : v.coeff (k - 2) = 0) (hv₁ : v.coeff (k - 1) = 0) :
    lowCharge u v = 0 := by
  exact cut_gap residue g f u v g_natDegree_le_two (le_of_eq f_natDegree)
    residue_g residue_f hk (fun i hi hik => hcycle i hi (by omega))
    hu₀ hu₁ hv₀ hv₁

/-- Swapped generators are also quadratic in their outer variable. -/
theorem swap_g : swap g =
    C (Y ^ 2) * (X : Bivariate) + C (Y ^ 2) * X ^ 2 + 1 := by
  simp only [swap, g, companion, BulkExactness.t, Y, map_add, map_mul,
    map_pow, map_one, Polynomial.Bivariate.swap_Y,
    Polynomial.Bivariate.swap_C, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X]
  ring

theorem swap_g_natDegree_le_two : (swap g).natDegree ≤ 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have hi₀ : i ≠ 0 := by omega
  have hi₁ : i ≠ 1 := by omega
  have hi₂ : 2 ≠ i := by omega
  rw [swap_g]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one,
    if_neg hi₀, if_neg (Ne.symm hi₁), if_neg (Ne.symm hi₂), mul_zero, add_zero]

/-- Residue in the swapped presentation: swap back before evaluating. -/
def columnResidue : Bivariate →+* ChargeAlgebra.A :=
  residue.comp swap.toRingHom

@[simp] theorem columnResidue_swap (p : Bivariate) :
    columnResidue (swap p) = residue p := by
  change residue (swap (swap p)) = residue p
  simp only [swap, Polynomial.Bivariate.swap_swap_apply]

/-- Low-column charge of the reflected physical pair in Proposition 8. -/
def lowColumnCharge (u v : Bivariate) : ChargeAlgebra.A :=
  columnResidue (below 2 (swap (g * u + f * v)))

/-- Dual cut lemma on reflected polynomials; reflection of the finite physical
code itself is a separate adapter, not an assumed symmetry. -/
theorem column_cut_gap (u v : Bivariate) {k : ℕ} (hk : 2 ≤ k) (hk' : k ≤ 19)
    (hcycle : ∀ i, 2 ≤ i → i ≤ 18 → (swap (g * u + f * v)).coeff i = 0)
    (hu₀ : (swap u).coeff (k - 2) = 0) (hu₁ : (swap u).coeff (k - 1) = 0)
    (hv₀ : (swap v).coeff (k - 2) = 0) (hv₁ : (swap v).coeff (k - 1) = 0) :
    lowColumnCharge u v = 0 := by
  have hc : ∀ i, 2 ≤ i → i < k →
      (swap g * swap u + swap f * swap v).coeff i = 0 := by
    intro i hi hik
    simpa only [map_add, map_mul] using hcycle i hi (by omega)
  have he := cut_gap columnResidue (swap g) (swap f) (swap u) (swap v)
    swap_g_natDegree_le_two (le_of_eq swap_f_natDegree)
    (by simp) (by simp) hk hc hu₀ hu₁ hv₀ hv₁
  simpa only [lowColumnCharge, map_add, map_mul] using he

end
end QldpcVerification.Planar.CutCharge
