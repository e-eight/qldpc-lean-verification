import QldpcVerification.Planar.RectangleFamilyPeeling

/-! Two empty physical rows imply an X boundary, by constructive peeling. -/
namespace QldpcVerification.Planar.RectangleFamilyGap

open Polynomial RectangleFamily RectangleFamilySyndrome RectangleFamilyMatrix
open RectangleFamilyPeeling

noncomputable section
variable {m n : ℕ}

def leftPart (w : V m n) (k : ℕ) : V m n :=
  fun q => if q.2.1.val < k then w q else 0

theorem leftPart_prefix (w : V m n) (k : ℕ) : PrefixSupported (leftPart w k) k := by
  intro b i j hi
  simp only [leftPart, if_neg (by omega : ¬ i.val < k)]

theorem left_row (w : V m n) (k : ℕ) (b : Bool) (i : ℕ) :
    (blockEncode m n b (leftPart w k)).coeff i =
      if i < k then (blockEncode m n b w).coeff i else 0 := by
  apply Polynomial.ext
  intro j
  by_cases hi : i < m + 2
  · by_cases hj : j < n + 2
    · rw [blockEncode_coeff (leftPart w k) b ⟨i, hi⟩ ⟨j, hj⟩]
      by_cases hik : i < k
      · rw [if_pos hik, blockEncode_coeff w b ⟨i, hi⟩ ⟨j, hj⟩]
        exact if_pos hik
      · rw [if_neg hik, coeff_zero]
        exact if_neg hik
    · have hz₁ := gridEncode_coeff_zero
        (fun a c => leftPart w k (b, (a, c))) i j (Or.inr (by omega : n + 2 ≤ j))
      have hz₂ := gridEncode_coeff_zero
        (fun a c => w (b, (a, c))) i j (Or.inr (by omega : n + 2 ≤ j))
      split_ifs <;> simpa only [blockEncode, LinearMap.coe_mk, AddHom.coe_mk,
        hz₁, hz₂, coeff_zero] using hz₁
  · have hz₁ := gridEncode_outer_zero (fun a c => leftPart w k (b, (a, c))) i (by omega)
    have hz₂ := gridEncode_outer_zero (fun a c => w (b, (a, c))) i (by omega)
    change ((gridEncode (m + 2) (n + 2) _).coeff i).coeff j = _
    rw [hz₁]
    split_ifs <;> simp only [blockEncode, LinearMap.coe_mk, AddHom.coe_mk, hz₂, coeff_zero]

theorem leftA (w : V m n) (k i : ℕ) :
    rowA (leftPart w k) i = if i < k then rowA w i else 0 := left_row w k false i

theorem leftB (w : V m n) (k i : ℕ) :
    rowB (leftPart w k) i = if i < k then rowB w i else 0 := left_row w k true i

theorem left_agree (w : V m n) {k i : ℕ} (hi : i < k + 2)
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) :
    rowA (leftPart w k) i = rowA w i ∧ rowB (leftPart w k) i = rowB w i := by
  rw [leftA, leftB]
  by_cases hik : i < k
  · simp [hik]
  · have he : i = k ∨ i = k + 1 := by omega
    rcases he with rfl | rfl
    · simp [ha₀, hb₀]
    · simp [ha₁, hb₁]

theorem leftPart_cycle (w : V m n) (hc : (HZ m n).mulVec w = 0) {k : ℕ}
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) :
    (HZ m n).mulVec (leftPart w k) = 0 := by
  apply (x_cycle_iff _).mpr
  intro i hi hi'
  have he₂ : i - 2 + 2 = i := by omega
  rw [fullSyndrome_apply, ← he₂, syndrome_coeff_add_two]
  change StripLocal.t * rowA (leftPart w k) (i - 2) +
    rowA (leftPart w k) (i - 2 + 2) + rowB (leftPart w k) (i - 2) +
    rowB (leftPart w k) (i - 2 + 1) + StripLocal.s * rowB (leftPart w k) (i - 2 + 2) = 0
  by_cases hik : i < k + 2
  · obtain ⟨ha0, hb0⟩ := left_agree w (by omega : i - 2 < k + 2) ha₀ ha₁ hb₀ hb₁
    obtain ⟨ha1, hb1⟩ := left_agree w (by omega : i - 2 + 1 < k + 2) ha₀ ha₁ hb₀ hb₁
    obtain ⟨ha2, hb2⟩ := left_agree w (by omega : i - 2 + 2 < k + 2) ha₀ ha₁ hb₀ hb₁
    rw [ha0, ha2, hb0, hb1, hb2]
    exact forward_recurrence w hc (i - 2) (by omega)
  · obtain ⟨ha0, hb0⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ i - 2)
    obtain ⟨ha1, hb1⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ i - 2 + 1)
    obtain ⟨ha2, hb2⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ i - 2 + 2)
    rw [ha0, ha2, hb0, hb1, hb2]
    simp

theorem rightPart_suffix (w : V m n) {k : ℕ}
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) :
    SuffixSupported (w - leftPart w k) (k + 2) := by
  intro b i j hi
  change w (b, (i, j)) - (if i.val < k then w (b, (i, j)) else 0) = 0
  by_cases hik : i.val < k
  · rw [if_pos hik, sub_self]
  · rw [if_neg hik, sub_zero]
    have he : i.val = k ∨ i.val = k + 1 := by omega
    cases b
    · rw [← rowA_coeff w i j]
      rcases he with he | he <;> rw [he]
      · rw [ha₀, coeff_zero]
      · rw [ha₁, coeff_zero]
    · rw [← rowB_coeff w i j]
      rcases he with he | he <;> rw [he]
      · rw [hb₀, coeff_zero]
      · rw [hb₁, coeff_zero]

/-- An actual cycle with a two-row gap is in the actual X row space. -/
theorem two_empty_rows_boundary (w : V m n) (hc : (HZ m n).mulVec w = 0)
    (k : ℕ) (hk : k + 1 < m + 2)
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) : w ∈ SX m n := by
  have hlc := leftPart_cycle w hc ha₀ ha₁ hb₀ hb₁
  have hl := prefix_fill k (by omega) (leftPart w k) hlc (leftPart_prefix w k)
  have hrc : (HZ m n).mulVec (w - leftPart w k) = 0 := by
    rw [Matrix.mulVec_sub, hc, hlc, sub_self]
  have hr := rightPart_suffix w ha₀ ha₁ hb₀ hb₁
  have he : m + 2 - (m - k) = k + 2 := by omega
  rw [← he] at hr
  have hrb := suffix_fill (m - k) (by omega) (w - leftPart w k) hrc hr
  have hadd := (SX m n).add_mem hrb hl
  simpa only [sub_add_cancel] using hadd

/-- No adjacent empty rows remain after passage to a nonzero logical class. -/
theorem x_adjacent (w : V m n) (hc : (HZ m n).mulVec w = 0) (hb : w ∉ SX m n)
    (k : ℕ) (hk : k + 1 < m + 2) :
    1 ≤ StripLocal.pairWt (rowA w k) (rowB w k) +
      StripLocal.pairWt (rowA w (k + 1)) (rowB w (k + 1)) := by
  by_contra h
  have ha₀ : rowA w k = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have hb₀ : rowB w k = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have ha₁ : rowA w (k + 1) = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have hb₁ : rowB w (k + 1) = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  exact hb (two_empty_rows_boundary w hc k hk ha₀ ha₁ hb₀ hb₁)

end
end QldpcVerification.Planar.RectangleFamilyGap
