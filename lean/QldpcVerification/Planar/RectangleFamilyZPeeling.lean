import QldpcVerification.Planar.RectangleFamilyGap

/-! The Z sector in reflected column coordinates; no X/Z code symmetry is assumed. -/
namespace QldpcVerification.Planar.RectangleFamilyZPeeling

open Polynomial RectangleFamily RectangleFamilySyndrome RectangleFamilyMatrix
open RectangleFamilyPeeling
open BoundaryRecurrence

noncomputable section
variable {m n : ℕ}

/-- The target coordinate is read as a reflected column of the original board. -/
def viewQ (m n : ℕ) : Q n m ≃ Q m n where
  toFun q := (!q.1, (q.2.2.rev, q.2.1.rev))
  invFun q := (!q.1, (q.2.2.rev, q.2.1.rev))
  left_inv q := by rcases q with ⟨b, i, j⟩; cases b <;> simp
  right_inv q := by rcases q with ⟨b, i, j⟩; cases b <;> simp

def view (m n : ℕ) : V m n ≃ₗ[ZMod 2] V n m where
  toFun w q := w (viewQ m n q)
  invFun w q := w ((viewQ m n).symm q)
  left_inv w := by funext q; simp
  right_inv w := by funext q; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem view_apply (w : V m n) (b : Bool)
    (i : Fin (n + 2)) (j : Fin (m + 2)) :
    view m n w (b, (i, j)) = w (!b, (j.rev, i.rev)) := rfl

@[simp] theorem view_involutive (w : V m n) : view n m (view m n w) = w := by
  funext q
  rcases q with ⟨b, i, j⟩
  cases b <;> simp

theorem view_weight (w : V m n) : hammingNorm (view m n w) = hammingNorm w := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact (viewQ m n).sum_comp (fun q => if w q ≠ 0 then 1 else 0)

/-- Z check synthesis written in the directional coordinates used for peeling. -/
def synthesis (m n : ℕ) : (Fin (m + 4) → Fin n → ZMod 2) →ₗ[ZMod 2] V m n :=
  (RectangleFamily.xPhysicalCoordinates m n).toLinearMap.comp
    (BoundaryRecurrence.zPhysical (m + 2) n)

def Stab (m n : ℕ) : Submodule (ZMod 2) (V m n) := LinearMap.range (synthesis m n)

def check (m n : ℕ) : V m n →ₗ[ZMod 2] (XAnchor n m → ZMod 2) :=
  (HX n m).mulVecLin.comp (view m n).toLinearMap

/-- The coordinate identity is checked on an abstract array, so the kernel
does not unfold the polynomial synthesis while reversing coordinates. -/
theorem view_physical (v : Fin (m + 2) → Fin (n + 2) → ZMod 2 × ZMod 2) :
    view m n (RectangleFamily.xPhysicalCoordinates m n v) =
      RectangleFamily.zPhysicalCoordinates n m v := by
  funext q
  rcases q with ⟨b, i, j⟩
  cases b <;> rfl

theorem view_synthesis (c : Fin (m + 4) → Fin n → ZMod 2) :
    view m n (synthesis m n c) =
      RectangleFamily.zSynthesis n m ((RectangleFamily.zAnchorCoordinates n m).symm c) := by
  have hc := (RectangleFamily.zAnchorCoordinates n m).apply_symm_apply c
  unfold RectangleFamily.zSynthesis
  change view m n ((RectangleFamily.xPhysicalCoordinates m n)
      (BoundaryRecurrence.zPhysical (m + 2) n c)) =
    (RectangleFamily.zPhysicalCoordinates n m)
      (BoundaryRecurrence.zPhysical (m + 2) n
        ((RectangleFamily.zAnchorCoordinates n m)
          ((RectangleFamily.zAnchorCoordinates n m).symm c)))
  rw [hc]
  exact view_physical (BoundaryRecurrence.zPhysical (m + 2) n c)

theorem synthesis_cycle (c : Fin (m + 4) → Fin n → ZMod 2) :
    check m n (synthesis m n c) = 0 := by
  change (HX n m).mulVec (view m n (synthesis m n c)) = 0
  rw [view_synthesis, RectangleFamily.zSynthesis_eq]
  change (HX n m).mulVec ((HZ n m).transpose.mulVec _) = 0
  rw [Matrix.mulVec_mulVec, RectangleFamily.commutation]
  simp

/-- Directional boundary membership is exactly original physical Z-row membership. -/
theorem stab_iff (w : V m n) :
    w ∈ Stab m n ↔ view m n w ∈ LinearMap.range (HZ n m).transpose.mulVecLin := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [view_synthesis, ← RectangleFamily.zSynthesis_eq]
    exact ⟨_, rfl⟩
  · rintro ⟨c, hc⟩
    refine ⟨RectangleFamily.zAnchorCoordinates n m c, ?_⟩
    apply (view m n).injective
    rw [view_synthesis]
    simp only [LinearEquiv.symm_apply_apply]
    rw [RectangleFamily.zSynthesis_eq]
    exact hc

theorem view_encoding (w : V m n) (b : Bool) :
    BulkExactness.swap (blockEncode n m b (reflectPhysical (view m n w))) =
      blockEncode m n b w := by
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  rw [BulkExactness.swap_coeff]
  by_cases hi : i < m + 2
  · by_cases hj : j < n + 2
    · rw [blockEncode_coeff _ b ⟨j, hj⟩ ⟨i, hi⟩,
        blockEncode_coeff w b ⟨i, hi⟩ ⟨j, hj⟩]
      cases b <;> simp
    · have hleft := gridEncode_coeff_zero
        (fun a c => reflectPhysical (view m n w) (b, (a, c))) j i
        (Or.inl (by omega : n + 2 ≤ j))
      have hright := gridEncode_coeff_zero (fun a c => w (b, (a, c))) i j
        (Or.inr (by omega : n + 2 ≤ j))
      exact hleft.trans hright.symm
  · have hleft := gridEncode_coeff_zero
      (fun a c => reflectPhysical (view m n w) (b, (a, c))) j i
      (Or.inr (by omega : m + 2 ≤ i))
    have hright := gridEncode_coeff_zero (fun a c => w (b, (a, c))) i j
      (Or.inl (by omega : m + 2 ≤ i))
    exact hleft.trans hright.symm

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
  have hg : BulkExactness.swap BulkExactness.g =
      C (BulkExactness.Y ^ 2) * (X : Bivariate) +
        C (BulkExactness.Y ^ 2) * X ^ 2 + 1 := by
    simp only [BulkExactness.swap, BulkExactness.g, BulkExactness.companion,
      BulkExactness.t, BulkExactness.Y, map_add, map_mul, map_pow, map_one,
      Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
    ring
  rw [map_add, map_mul, map_mul, hg, BulkExactness.swap_f]
  simp only [BulkExactness.Y, StripLocal.t, StripLocal.s, add_mul, mul_assoc,
    one_mul, coeff_add, coeff_C_mul, coeff_X_pow_mul, hx]
  ring

theorem syndrome_view (w : V m n) (j : ℕ) :
    (BulkExactness.swap (fullSyndrome n m (reflectPhysical (view m n w)))).coeff (j + 2) =
      rowA w (j + 2) + StripLocal.s * rowA w (j + 1) +
        StripLocal.s * rowA w j + rowB w j + StripLocal.t * rowB w (j + 2) := by
  rw [fullSyndrome_apply, swapped_syndrome_coeff_add_two]
  change (BulkExactness.swap (blockEncode n m false (reflectPhysical (view m n w)))).coeff (j + 2) +
    StripLocal.s * (BulkExactness.swap (blockEncode n m false (reflectPhysical (view m n w)))).coeff (j + 1) +
    StripLocal.s * (BulkExactness.swap (blockEncode n m false (reflectPhysical (view m n w)))).coeff j +
    (BulkExactness.swap (blockEncode n m true (reflectPhysical (view m n w)))).coeff j +
    StripLocal.t * (BulkExactness.swap (blockEncode n m true (reflectPhysical (view m n w)))).coeff (j + 2) = _
  simp only [view_encoding]
  rfl

theorem backward_recurrence (w : V m n) (hc : check m n w = 0)
    (j : ℕ) (hj : j + 2 ≤ m + 1) :
    rowA w (j + 2) + StripLocal.s * rowA w (j + 1) + StripLocal.s * rowA w j +
      rowB w j + StripLocal.t * rowB w (j + 2) = 0 := by
  have h := z_cycle_coeff (view m n w) hc (j + 2) (by omega) hj
  rw [syndrome_view] at h
  exact h

theorem cycle_of_recurrence (w : V m n)
    (h : ∀ j, j + 2 ≤ m + 1 →
      rowA w (j + 2) + StripLocal.s * rowA w (j + 1) + StripLocal.s * rowA w j +
        rowB w j + StripLocal.t * rowB w (j + 2) = 0) : check m n w = 0 := by
  apply (z_cycle_iff (view m n w)).mpr
  intro i hi hi'
  have he : i - 2 + 2 = i := by omega
  rw [← he, syndrome_view]
  exact h (i - 2) (by omega)

theorem prefix_last_relation (w : V m n) {r : ℕ} (hr : r + 1 ≤ m)
    (hc : check m n w = 0) (hs : PrefixSupported w (r + 1)) :
    rowB w r = StripLocal.s * rowA w r := by
  have h := backward_recurrence w hc r (by omega)
  obtain ⟨ha₁, hb₁⟩ := prefix_row_zero w hs (by omega : r + 1 ≤ r + 1)
  obtain ⟨ha₂, hb₂⟩ := prefix_row_zero w hs (by omega : r + 1 ≤ r + 2)
  rw [ha₂, ha₁, hb₂] at h
  simp only [zero_add, add_zero, mul_zero] at h
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h

theorem prefix_last_supported (w : V m n) {r : ℕ} (hr : r + 1 ≤ m)
    (hc : check m n w = 0) (hs : PrefixSupported w (r + 1)) :
    supportedBelow n (rowA w r) := by
  apply RectangleFamilyPeeling.factor_support StripLocal.s _
    (pow_ne_zero 2 Polynomial.X_ne_zero) (Polynomial.natDegree_X_pow 2)
  rw [← prefix_last_relation w hr hc hs]
  exact row_supported w true r

def packet (m n k : ℕ) (h : RectangleFamilyPeeling.P) : V m n :=
  synthesis m n (fun i j => if i.val = k then h.coeff j.val else 0)

theorem packet_entry {k : ℕ} (hk : k < m + 4) (h : RectangleFamilyPeeling.P)
    (hh : supportedBelow n h) (i : ℕ) :
    entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) i =
      if i = k then h else 0 :=
  RectangleFamilyPeeling.packet_entry hk h hh i

theorem packet_apply {k : ℕ} (hk : k < m + 4) (h : RectangleFamilyPeeling.P)
    (hh : supportedBelow n h) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    packet m n k h (false, (i, j)) =
      ((if i.val = k then h else 0) +
        StripLocal.t * (if i.val + 2 = k then h else 0)).coeff j.val ∧
    packet m n k h (true, (i, j)) =
      ((if i.val + 2 = k then h else 0) +
        StripLocal.s * (if i.val + 1 = k then h else 0) +
        StripLocal.s * (if i.val = k then h else 0)).coeff j.val := by
  constructor
  · change (entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) i.val +
      ((X : RectangleFamilyPeeling.P) + X ^ 2) *
        entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) (i.val + 2)).coeff j.val = _
    simp only [packet_entry hk h hh, StripLocal.t]
  · change (entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) (i.val + 2) +
      (X : RectangleFamilyPeeling.P) ^ 2 *
        entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) (i.val + 1) +
      (X : RectangleFamilyPeeling.P) ^ 2 *
        entry (pack (m + 4) n (fun a b => if a.val = k then h.coeff b.val else 0)) i.val).coeff j.val = _
    simp only [packet_entry hk h hh, StripLocal.s]

theorem packet_mem (m n k : ℕ) (h : RectangleFamilyPeeling.P) :
    packet m n k h ∈ Stab m n := ⟨_, rfl⟩

theorem packet_cycle (m n k : ℕ) (h : RectangleFamilyPeeling.P) :
    check m n (packet m n k h) = 0 := synthesis_cycle _

/-- A cycle supported away from the right boundary is an Z stabilizer in directional coordinates. -/
theorem prefix_fill (r : ℕ) (hr : r ≤ m) (w : V m n)
    (hc : check m n w = 0) (hs : PrefixSupported w r) : w ∈ Stab m n := by
  induction r generalizing w with
  | zero =>
    have hz : w = 0 := by
      funext q
      exact hs q.1 q.2.1 q.2.2 (Nat.zero_le _)
    rw [hz]
    exact (Stab m n).zero_mem
  | succ r ih =>
    have hh := prefix_last_supported w hr hc hs
    let p := packet m n r (rowA w r)
    have hp : p ∈ Stab m n := packet_mem m n r (rowA w r)
    have hpc : check m n p = 0 := packet_cycle m n r (rowA w r)
    have hc' : check m n (w - p) = 0 := by
      rw [map_sub, hc, hpc, sub_self]
    have hs' : PrefixSupported (w - p) r := by
      intro b i j hi
      have he := packet_apply (m := m) (n := n) (by omega : r < m + 4) (rowA w r) hh i j
      by_cases hir : i.val = r
      · have hne₁ : i.val + 1 ≠ r := by omega
        have hne₂ : i.val + 2 ≠ r := by omega
        simp only [if_pos hir, if_neg hne₁, if_neg hne₂, mul_zero, add_zero, zero_add] at he
        have hrel := prefix_last_relation w hr hc hs
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [show p (false, (i, j)) = (rowA w r).coeff j.val from he.1]
          rw [← hir, rowA_coeff, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [show p (true, (i, j)) = (StripLocal.s * rowA w r).coeff j.val from he.2,
            ← hrel, ← hir, rowB_coeff, sub_self]
      · have hne₁ : i.val + 1 ≠ r := by omega
        have hne₂ : i.val + 2 ≠ r := by omega
        simp only [if_neg hir, if_neg hne₁, if_neg hne₂, mul_zero, add_zero, zero_add, coeff_zero] at he
        have hw := hs b i j (by omega)
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [hw, show p (false, (i, j)) = 0 from he.1, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [hw, show p (true, (i, j)) = 0 from he.2, sub_self]
    have hmem := ih (by omega) (w - p) hc' hs'
    have hadd := (Stab m n).add_mem hmem hp
    simpa only [sub_add_cancel] using hadd


theorem suffix_first_relation (w : V m n) {r : ℕ} (hr : 2 ≤ r) (hr' : r < m + 2)
    (hc : check m n w = 0) (hs : SuffixSupported w r) :
    rowA w r = StripLocal.t * rowB w r := by
  have h := backward_recurrence w hc (r - 2) (by omega)
  obtain ⟨ha₀, hb₀⟩ := suffix_row_zero w hs (by omega : r - 2 < r)
  obtain ⟨ha₁, hb₁⟩ := suffix_row_zero w hs (by omega : r - 1 < r)
  have he₂ : r - 2 + 2 = r := by omega
  have he₁ : r - 2 + 1 = r - 1 := by omega
  rw [he₂, he₁, ha₀, ha₁, hb₀] at h
  simp only [add_zero, mul_zero] at h
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h

theorem suffix_first_supported (w : V m n) {r : ℕ} (hr : 2 ≤ r) (hr' : r < m + 2)
    (hc : check m n w = 0) (hs : SuffixSupported w r) :
    supportedBelow n (rowB w r) := by
  apply RectangleFamilyPeeling.factor_support StripLocal.t _ StripLocal.t_ne_zero
    RectangleFamilyPeeling.t_natDegree
  rw [← suffix_first_relation w hr hr' hc hs]
  exact row_supported w false r

/-- A cycle supported away from the left boundary is an Z stabilizer in directional coordinates. -/
theorem suffix_fill (r : ℕ) (hr : r ≤ m) (w : V m n)
    (hc : check m n w = 0) (hs : SuffixSupported w (m + 2 - r)) :
    w ∈ Stab m n := by
  induction r generalizing w with
  | zero =>
    have hz : w = 0 := by
      funext q
      exact hs q.1 q.2.1 q.2.2 (by have := q.2.1.isLt; omega)
    rw [hz]
    exact (Stab m n).zero_mem
  | succ r ih =>
    let k := m + 2 - (r + 1)
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hk' : k < m + 2 := by dsimp [k]; omega
    have hh := suffix_first_supported w hk hk' hc hs
    let p := packet m n (k + 2) (rowB w k)
    have hp : p ∈ Stab m n := packet_mem m n (k + 2) (rowB w k)
    have hpc : check m n p = 0 := packet_cycle m n (k + 2) (rowB w k)
    have hc' : check m n (w - p) = 0 := by
      rw [map_sub, hc, hpc, sub_self]
    have hs' : SuffixSupported (w - p) (m + 2 - r) := by
      intro b i j hi
      have hik : i.val ≤ k := by dsimp [k]; omega
      have he := packet_apply (m := m) (n := n) (by omega : k + 2 < m + 4)
        (rowB w k) hh i j
      have hne₀ : i.val ≠ k + 2 := by omega
      have hne₁ : i.val + 1 ≠ k + 2 := by omega
      by_cases hir : i.val = k
      · have he₂ : i.val + 2 = k + 2 := by omega
        simp only [if_neg hne₀, if_neg hne₁, if_pos he₂, mul_zero,
          zero_add, add_zero] at he
        have hrel := suffix_first_relation w hk hk' hc hs
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [show p (false, (i, j)) = (StripLocal.t * rowB w k).coeff j.val from he.1,
            ← hrel, ← hir, rowA_coeff, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [show p (true, (i, j)) = (rowB w k).coeff j.val from he.2]
          rw [← hir, rowB_coeff, sub_self]
      · have hne₂ : i.val + 2 ≠ k + 2 := by omega
        simp only [if_neg hne₀, if_neg hne₁, if_neg hne₂, mul_zero,
          zero_add, add_zero, coeff_zero] at he
        have hw := hs b i j (by dsimp [k] at hik hir; omega)
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [hw, show p (false, (i, j)) = 0 from he.1, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [hw, show p (true, (i, j)) = 0 from he.2, sub_self]
    have hmem := ih (by omega) (w - p) hc' hs'
    have hadd := (Stab m n).add_mem hmem hp
    simpa only [sub_add_cancel] using hadd


end
end QldpcVerification.Planar.RectangleFamilyZPeeling
