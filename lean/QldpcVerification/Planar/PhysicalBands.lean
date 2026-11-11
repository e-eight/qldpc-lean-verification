import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Physical support counting for disjoint bands. No code-specific detection
hypothesis is supplied by this module. -/

namespace QldpcVerification.Planar.PhysicalBands

/-- Counting all adjacent pairs preserves the contribution of the two endpoints. -/
theorem adjacent_pair_bound (w : ℕ → ℕ)
    (h : ∀ i < 18, 1 ≤ w i + w (i + 1)) :
    18 + w 0 + w 18 ≤ 2 * ∑ i ∈ Finset.range 19, w i := by
  have hs : (∑ _i ∈ Finset.range 18, 1 : ℕ) ≤
      ∑ i ∈ Finset.range 18, (w i + w (i + 1)) :=
    Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    Finset.sum_add_distrib] at hs
  have hlo := Finset.sum_range_succ' w 18
  have hhi := Finset.sum_range_succ w 18
  norm_num only at hlo hhi
  omega

theorem adjacent_pair_rounded_bound (w : ℕ → ℕ)
    (h : ∀ i < 18, 1 ≤ w i + w (i + 1)) :
    9 + (w 0 + w 18 + 1) / 2 ≤ ∑ i ∈ Finset.range 19, w i := by
  have hb := adjacent_pair_bound w h
  omega

/-- If every label occurs on the physical support, there are at least as many
nonzero coordinates as labels. -/
theorem weight_ge_labels {Q I : Type*} [Fintype Q] [Fintype I]
    (x : Q → ZMod 2) (label : Q → I)
    (h : ∀ i, ∃ q, x q ≠ 0 ∧ label q = i) :
    Fintype.card I ≤ hammingNorm x := by
  classical
  let f : {q : Q // x q ≠ 0} → I := fun q => label q.val
  have hf : Function.Surjective f := by
    intro i
    obtain ⟨q, hq, hi⟩ := h i
    exact ⟨⟨q, hq⟩, hi⟩
  have hc := Fintype.card_le_of_surjective f hf
  simpa only [Fintype.card_subtype, hammingNorm] using hc

abbrev Q := Bool × (Fin 19 × Fin 19)

/-- Nine disjoint row pairs, with the unused last row assigned to the last label. -/
def rowLabel (q : Q) : Fin 9 := ⟨min (q.2.1.val / 2) 8, by omega⟩

theorem row_weight_ge_nine (x : Q → ZMod 2)
    (h : ∀ i : Fin 9, ∃ q, x q ≠ 0 ∧
      (q.2.1.val = 2 * i.val ∨ q.2.1.val = 2 * i.val + 1)) :
    9 ≤ hammingNorm x := by
  apply weight_ge_labels x rowLabel
  intro i
  obtain ⟨q, hq, hi⟩ := h i
  refine ⟨q, hq, ?_⟩
  apply Fin.ext
  change min (q.2.1.val / 2) 8 = i.val
  have hb := i.isLt
  omega

/-- The identical counting statement for disjoint column pairs. -/
theorem column_weight_ge_nine (x : Q → ZMod 2)
    (h : ∀ i : Fin 9, ∃ q, x q ≠ 0 ∧
      (q.2.2.val = 2 * i.val ∨ q.2.2.val = 2 * i.val + 1)) :
    9 ≤ hammingNorm x := by
  let label : Q → Fin 9 := fun q => ⟨min (q.2.2.val / 2) 8, by omega⟩
  apply weight_ge_labels x label
  intro i
  obtain ⟨q, hq, hi⟩ := h i
  refine ⟨q, hq, ?_⟩
  apply Fin.ext
  change min (q.2.2.val / 2) 8 = i.val
  have hb := i.isLt
  omega

end QldpcVerification.Planar.PhysicalBands
