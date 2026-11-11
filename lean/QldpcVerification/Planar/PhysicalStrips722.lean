import QldpcVerification.Planar.Syndrome722
import QldpcVerification.Planar.SyndromeMatrix722
import QldpcVerification.Planar.StripLocal
import QldpcVerification.Planar.CutCharge
import QldpcVerification.Planar.ChargeCompleteness722

/-!
# Actual physical vectors as polynomial strips

Forward strips are rows of the two encoded physical blocks. Backward strips
are columns after the proved physical reflection, implemented by swapping
polynomial variables. Weight identities count coefficient supports using the
proved finite support bounds and literal coefficient readout. The recurrence
identities hold universally for ordinary bivariate polynomials; actual matrix
cycles supply their zero coefficients through `SyndromeMatrix722`.

Adjacent nonemptiness is derived for actual nonstabilizer cycles using the
complete logical charges and the cut-gap lemmas. No coefficient correspondence,
weight preservation, or nonzero-charge premise is assumed.

Replay and guarded axiom checking belong to the main capped runner.
-/

namespace QldpcVerification.Planar.PhysicalStrips722

open Polynomial Syndrome722 SyndromeMatrix722 Commutation StripLocal
open scoped CharTwo

noncomputable section

def forwardA (w : physicalV) (i : ℕ) : StripLocal.P := (encode w).1.coeff i
def forwardB (w : physicalV) (i : ℕ) : StripLocal.P := (encode w).2.coeff i

def backwardA (w : physicalV) (i : ℕ) : StripLocal.P :=
  (BulkExactness.swap (encode (reflectPhysical w)).1).coeff i
def backwardB (w : physicalV) (i : ℕ) : StripLocal.P :=
  (BulkExactness.swap (encode (reflectPhysical w)).2).coeff i

/-- A bounded polynomial's support cardinality is exactly the finite sum of
its nonzero coefficient indicators. This is not a degree or weight estimate. -/
theorem wt_eq_sum_fin (p : StripLocal.P) (n : ℕ)
    (hp : ∀ j, n ≤ j → p.coeff j = 0) :
    wt p = ∑ j : Fin n, if p.coeff j.val ≠ 0 then 1 else 0 := by
  classical
  have hs : p.support = (Finset.range n).filter (fun j => p.coeff j ≠ 0) := by
    ext j
    simp only [Polynomial.mem_support_iff, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hj
      exact ⟨by by_contra hn; exact hj (hp j (by omega)), hj⟩
    · exact fun hj => hj.2
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if p.coeff j ≠ 0 then 1 else 0) n]
  simp only [wt, hs, Finset.card_filter]

theorem block_coeff_zero (w : physicalV) (b : Bool) (i j : ℕ)
    (hout : 19 ≤ i ∨ 19 ≤ j) :
    ((blockEncode b w).coeff i).coeff j = 0 :=
  squareEncode_coeff_zero _ i j hout

/-- One row's polynomial weight counts its actual physical coordinates. -/
theorem block_slice_weight (w : physicalV) (b : Bool) (i : Fin 19) :
    wt ((blockEncode b w).coeff i.val) =
      ∑ j : Fin 19, if w (b, (i, j)) ≠ 0 then 1 else 0 := by
  rw [wt_eq_sum_fin _ 19 (fun j hj => block_coeff_zero w b i.val j (Or.inr hj))]
  simp only [blockEncode_coeff]

/-- The analogous column count uses the universal variable-swap identity. -/
theorem swapped_block_slice_weight (w : physicalV) (b : Bool) (i : Fin 19) :
    wt ((BulkExactness.swap (blockEncode b w)).coeff i.val) =
      ∑ j : Fin 19, if w (b, (j, i)) ≠ 0 then 1 else 0 := by
  rw [wt_eq_sum_fin _ 19 (fun j hj => by
    rw [BulkExactness.swap_coeff]
    exact block_coeff_zero w b j i.val (Or.inl hj))]
  simp only [BulkExactness.swap_coeff, blockEncode_coeff]

/-- Prove product-index counting while the coordinate types are abstract, so
simplification never unfolds a concrete board's finite enumeration. -/
theorem hammingNorm_bool_prod {I J : Type*} [Fintype I] [Fintype J]
    (w : Bool × (I × J) → Commutation.F2) :
    hammingNorm w =
      (∑ i : I, ∑ j : J, if w (false, (i, j)) ≠ 0 then 1 else 0) +
      (∑ i : I, ∑ j : J, if w (true, (i, j)) ≠ 0 then 1 else 0) := by
  classical
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

/-- Product-index counting, with no expansion of the 722 coordinates. -/
theorem physical_weight_sum (w : physicalV) :
    hammingNorm w =
      (∑ i : Fin 19, ∑ j : Fin 19, if w (false, (i, j)) ≠ 0 then 1 else 0) +
      (∑ i : Fin 19, ∑ j : Fin 19, if w (true, (i, j)) ≠ 0 then 1 else 0) :=
  hammingNorm_bool_prod w

/-- The nineteen forward pair weights total exactly the physical Hamming weight. -/
theorem forward_weight (w : physicalV) :
    (∑ i ∈ Finset.range 19, pairWt (forwardA w i) (forwardB w i)) = hammingNorm w := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => pairWt (forwardA w i) (forwardB w i)) 19]
  rw [physical_weight_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change wt ((blockEncode false w).coeff i.val) +
    wt ((blockEncode true w).coeff i.val) = _
  rw [block_slice_weight, block_slice_weight]

/-- Swapping variables exchanges the two finite sums; reflection preserves
physical weight by the already-proved coordinate equivalence. -/
theorem backward_weight (w : physicalV) :
    (∑ i ∈ Finset.range 19, pairWt (backwardA w i) (backwardB w i)) = hammingNorm w := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => pairWt (backwardA w i) (backwardB w i)) 19]
  have hcomm (b : Bool) :
      (∑ i : Fin 19, ∑ j : Fin 19,
        if reflectPhysical w (b, (j, i)) ≠ 0 then 1 else 0) =
      (∑ i : Fin 19, ∑ j : Fin 19,
        if reflectPhysical w (b, (i, j)) ≠ 0 then 1 else 0) := Finset.sum_comm
  rw [← reflectPhysical_weight w, physical_weight_sum, ← hcomm false, ← hcomm true,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change wt ((BulkExactness.swap (blockEncode false (reflectPhysical w))).coeff i.val) +
    wt ((BulkExactness.swap (blockEncode true (reflectPhysical w))).coeff i.val) = _
  rw [swapped_block_slice_weight, swapped_block_slice_weight]

/-- Universal full-syndrome coefficient identity in the forward orientation.
The shifted index avoids any truncated natural-number subtraction. -/
theorem syndrome_coeff_add_two (u v : Bivariate) (j : ℕ) :
    (BulkExactness.g * u + BulkExactness.f * v).coeff (j + 2) =
      StripLocal.t * u.coeff j + u.coeff (j + 2) + v.coeff j +
        v.coeff (j + 1) + StripLocal.s * v.coeff (j + 2) := by
  have hx : (X * v).coeff (j + 2) = v.coeff (j + 1) :=
    Polynomial.coeff_X_mul v (j + 1)
  simp only [BulkExactness.g, BulkExactness.companion, BulkExactness.f,
    BulkExactness.quadratic, BulkExactness.t, BulkExactness.Y, StripLocal.t,
    StripLocal.s, add_mul, mul_assoc, one_mul, coeff_add, coeff_C_mul,
    coeff_X_pow_mul, hx]
  ring

/-- Universal coefficient identity for the swapped syndrome. In particular
the coefficient multiplying the current B slice is `X+X²`, not `X²`. -/
theorem swapped_syndrome_coeff_add_two (u v : Bivariate) (j : ℕ) :
    (BulkExactness.swap (BulkExactness.g * u + BulkExactness.f * v)).coeff (j + 2) =
      (BulkExactness.swap u).coeff (j + 2) +
        StripLocal.s * (BulkExactness.swap u).coeff (j + 1) +
        StripLocal.s * (BulkExactness.swap u).coeff j +
        (BulkExactness.swap v).coeff j +
        StripLocal.t * (BulkExactness.swap v).coeff (j + 2) := by
  have hx : (X * BulkExactness.swap u).coeff (j + 2) =
      (BulkExactness.swap u).coeff (j + 1) :=
    Polynomial.coeff_X_mul (BulkExactness.swap u) (j + 1)
  rw [map_add, map_mul, map_mul, CutCharge.swap_g, BulkExactness.swap_f]
  simp only [BulkExactness.Y, StripLocal.t, StripLocal.s, add_mul, mul_assoc,
    one_mul, coeff_add, coeff_C_mul, coeff_X_pow_mul, hx]
  ring

/-- Actual HZ cycles satisfy the forward strip recurrence, at indices 2..18. -/
theorem forward_recurrence_add_two (w : physicalV) (hc : HZ.mulVec w = 0)
    (j : ℕ) (hj : j + 2 ≤ 18) :
    forwardA w (j + 2) = StripLocal.t * forwardA w j + forwardB w (j + 1) +
      forwardB w j + StripLocal.s * forwardB w (j + 2) := by
  have hz := x_cycle_coeff w hc (j + 2) (by omega) hj
  rw [fullSyndrome_apply, syndrome_coeff_add_two] at hz
  dsimp [forwardA, forwardB]
  linear_combination (norm := (ring_nf <;> simp)) hz

/-- Actual HX cycles satisfy the backward recurrence on reflected columns. -/
theorem backward_recurrence_add_two (w : physicalV) (hc : HX.mulVec w = 0)
    (j : ℕ) (hj : j + 2 ≤ 18) :
    StripLocal.t * backwardB w (j + 2) = backwardA w (j + 2) +
      StripLocal.s * backwardA w (j + 1) + StripLocal.s * backwardA w j +
      backwardB w j := by
  have hz := z_cycle_coeff w hc (j + 2) (by omega) hj
  rw [fullSyndrome_apply, swapped_syndrome_coeff_add_two] at hz
  dsimp [backwardA, backwardB]
  linear_combination (norm := (ring_nf <;> simp)) hz

/-- Subtraction-index form matching the strip draft. -/
theorem forward_recurrence (w : physicalV) (hc : HZ.mulVec w = 0)
    (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 18) :
    forwardA w i = StripLocal.t * forwardA w (i - 2) + forwardB w (i - 1) +
      forwardB w (i - 2) + StripLocal.s * forwardB w i := by
  have h := forward_recurrence_add_two w hc (i - 2) (by omega)
  have h₂ : i - 2 + 2 = i := by omega
  have h₁ : i - 2 + 1 = i - 1 := by omega
  simpa only [h₂, h₁] using h

theorem backward_recurrence (w : physicalV) (hc : HX.mulVec w = 0)
    (i : ℕ) (hi : 2 ≤ i) (hi' : i ≤ 18) :
    StripLocal.t * backwardB w i = backwardA w i + StripLocal.s * backwardA w (i - 1) +
      StripLocal.s * backwardA w (i - 2) + backwardB w (i - 2) := by
  have h := backward_recurrence_add_two w hc (i - 2) (by omega)
  have h₂ : i - 2 + 2 = i := by omega
  have h₁ : i - 2 + 1 = i - 1 := by omega
  simpa only [h₂, h₁] using h

/-- Adjacent rows of an actual nonstabilizer HZ cycle cannot both be empty.
The nonzero charge is a consequence of completeness, not an extra premise. -/
theorem forward_adjacent (w : physicalV) (hc : HZ.mulVec w = 0)
    (hb : w ∉ CycleSpaces722.xStab) (i : ℕ) (hi : i + 1 < 19) :
    1 ≤ pairWt (forwardA w i) (forwardB w i) +
      pairWt (forwardA w (i + 1)) (forwardB w (i + 1)) := by
  by_contra h
  have ha₀ : forwardA w i = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have hb₀ : forwardB w i = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have ha₁ : forwardA w (i + 1) = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have hb₁ : forwardB w (i + 1) = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  apply ChargeCompleteness722.x_detects w hc hb
  have h₂ : i + 2 - 2 = i := by omega
  have h₁ : i + 2 - 1 = i + 1 := by omega
  apply CutCharge.row_cut_gap (encode w).1 (encode w).2
    (k := i + 2) (by omega) (by omega)
  · exact fun j hj hj' => x_cycle_coeff w hc j hj hj'
  · simpa only [h₂] using ha₀
  · simpa only [h₁] using ha₁
  · simpa only [h₂] using hb₀
  · simpa only [h₁] using hb₁

/-- Adjacent reflected columns of an actual nonstabilizer HX cycle are
nonempty, by the transported column charge and its proved completeness. -/
theorem backward_adjacent (w : physicalV) (hc : HX.mulVec w = 0)
    (hb : w ∉ CycleSpaces722.zStab) (i : ℕ) (hi : i + 1 < 19) :
    1 ≤ pairWt (backwardA w i) (backwardB w i) +
      pairWt (backwardA w (i + 1)) (backwardB w (i + 1)) := by
  by_contra h
  have ha₀ : backwardA w i = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have hb₀ : backwardB w i = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have ha₁ : backwardA w (i + 1) = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  have hb₁ : backwardB w (i + 1) = 0 := wt_eq_zero.mp (by unfold pairWt at h; omega)
  apply ChargeCompleteness722.z_detects w hc hb
  have h₂ : i + 2 - 2 = i := by omega
  have h₁ : i + 2 - 1 = i + 1 := by omega
  apply CutCharge.column_cut_gap (encode (reflectPhysical w)).1
    (encode (reflectPhysical w)).2 (k := i + 2) (by omega) (by omega)
  · exact fun j hj hj' => z_cycle_coeff w hc j hj hj'
  · simpa only [h₂] using ha₀
  · simpa only [h₁] using ha₁
  · simpa only [h₂] using hb₀
  · simpa only [h₁] using hb₁

end
end QldpcVerification.Planar.PhysicalStrips722
