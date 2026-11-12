import QldpcVerification.Planar.RectangleFamilyZPeeling

/-! Empty-column exactness for actual Z logicals. -/
namespace QldpcVerification.Planar.RectangleFamilyZGap

open Polynomial RectangleFamily RectangleFamilySyndrome RectangleFamilyMatrix
open RectangleFamilyPeeling RectangleFamilyGap RectangleFamilyZPeeling

noncomputable section
variable {m n : ℕ}

theorem leftPart_cycle (w : V m n) (hc : check m n w = 0) {k : ℕ}
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) :
    check m n (leftPart w k) = 0 := by
  apply cycle_of_recurrence
  intro j hj
  by_cases hjk : j + 2 < k + 2
  · obtain ⟨ha0, hb0⟩ := left_agree w (by omega : j < k + 2) ha₀ ha₁ hb₀ hb₁
    obtain ⟨ha1, hb1⟩ := left_agree w (by omega : j + 1 < k + 2) ha₀ ha₁ hb₀ hb₁
    obtain ⟨ha2, hb2⟩ := left_agree w (by omega : j + 2 < k + 2) ha₀ ha₁ hb₀ hb₁
    rw [ha2, ha1, ha0, hb0, hb2]
    exact backward_recurrence w hc j hj
  · obtain ⟨ha0, hb0⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ j)
    obtain ⟨ha1, hb1⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ j + 1)
    obtain ⟨ha2, hb2⟩ := prefix_row_zero _ (leftPart_prefix w k) (by omega : k ≤ j + 2)
    rw [ha2, ha1, ha0, hb0, hb2]
    simp

/-- A directional Z cycle with two empty slices belongs to the actual Z boundary image. -/
theorem two_empty_slices_boundary (w : V m n) (hc : check m n w = 0)
    (k : ℕ) (hk : k + 1 < m + 2)
    (ha₀ : rowA w k = 0) (ha₁ : rowA w (k + 1) = 0)
    (hb₀ : rowB w k = 0) (hb₁ : rowB w (k + 1) = 0) : w ∈ Stab m n := by
  have hlc := leftPart_cycle w hc ha₀ ha₁ hb₀ hb₁
  have hl := RectangleFamilyZPeeling.prefix_fill k (by omega) (leftPart w k) hlc (leftPart_prefix w k)
  have hrc : check m n (w - leftPart w k) = 0 := by
    rw [map_sub, hc, hlc, sub_self]
  have hr := rightPart_suffix w ha₀ ha₁ hb₀ hb₁
  have he : m + 2 - (m - k) = k + 2 := by omega
  rw [← he] at hr
  have hrb := RectangleFamilyZPeeling.suffix_fill (m - k) (by omega) (w - leftPart w k) hrc hr
  have hadd := (Stab m n).add_mem hrb hl
  simpa only [sub_add_cancel] using hadd

theorem adjacent_directional (w : V m n) (hc : check m n w = 0) (hb : w ∉ Stab m n)
    (k : ℕ) (hk : k + 1 < m + 2) :
    1 ≤ StripLocal.pairWt (rowA w k) (rowB w k) +
      StripLocal.pairWt (rowA w (k + 1)) (rowB w (k + 1)) := by
  by_contra h
  have ha₀ : rowA w k = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have hb₀ : rowB w k = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have ha₁ : rowA w (k + 1) = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  have hb₁ : rowB w (k + 1) = 0 := StripLocal.wt_eq_zero.mp (by unfold StripLocal.pairWt at h; omega)
  exact hb (two_empty_slices_boundary w hc k hk ha₀ ha₁ hb₀ hb₁)

def columnA (w : V m n) (i : ℕ) : RectangleFamilyPeeling.P := rowA (view m n w) i
def columnB (w : V m n) (i : ℕ) : RectangleFamilyPeeling.P := rowB (view m n w) i

theorem view_cycle (w : V m n) (hc : (HX m n).mulVec w = 0) :
    check n m (view m n w) = 0 := by
  change (HX m n).mulVec (view n m (view m n w)) = 0
  rw [view_involutive]
  exact hc

theorem view_nonboundary (w : V m n)
    (hb : w ∉ LinearMap.range (HZ m n).transpose.mulVecLin) :
    view m n w ∉ Stab n m := by
  intro h
  have he := (stab_iff (view m n w)).mp h
  rw [view_involutive] at he
  exact hb he

/-- Actual nonboundary X-check cycles occupy every adjacent pair of reflected columns. -/
theorem z_adjacent (w : V m n) (hc : (HX m n).mulVec w = 0)
    (hb : w ∉ LinearMap.range (HZ m n).transpose.mulVecLin)
    (k : ℕ) (hk : k + 1 < n + 2) :
    1 ≤ StripLocal.pairWt (columnA w k) (columnB w k) +
      StripLocal.pairWt (columnA w (k + 1)) (columnB w (k + 1)) :=
  adjacent_directional (view m n w) (view_cycle w hc) (view_nonboundary w hb) k hk

/-- The backward recurrence has no implicit symmetry or charge assumption. -/
theorem z_recurrence (w : V m n) (hc : (HX m n).mulVec w = 0)
    (j : ℕ) (hj : j + 2 ≤ n + 1) :
    columnA w (j + 2) + StripLocal.s * columnA w (j + 1) +
      StripLocal.s * columnA w j + columnB w j + StripLocal.t * columnB w (j + 2) = 0 :=
  backward_recurrence (view m n w) (view_cycle w hc) j hj

end
end QldpcVerification.Planar.RectangleFamilyZGap
