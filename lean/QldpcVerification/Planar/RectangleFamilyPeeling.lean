import QldpcVerification.Planar.RectangleFamilyMatrix
import QldpcVerification.Planar.StripLocal

/-! Constructive elimination of one-sided cycles. -/
namespace QldpcVerification.Planar.RectangleFamilyPeeling

open Polynomial RectangleFamily RectangleFamilySyndrome RectangleFamilyMatrix
open BoundaryRecurrence

noncomputable section

variable {m n : ℕ}

abbrev P := Polynomial (ZMod 2)

def rowA (w : V m n) (i : ℕ) : P := (encode m n w).1.coeff i
def rowB (w : V m n) (i : ℕ) : P := (encode m n w).2.coeff i

theorem rowA_coeff (w : V m n) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    (rowA w i.val).coeff j.val = w (false, (i, j)) := blockEncode_coeff w false i j

theorem rowB_coeff (w : V m n) (i : Fin (m + 2)) (j : Fin (n + 2)) :
    (rowB w i.val).coeff j.val = w (true, (i, j)) := blockEncode_coeff w true i j

theorem row_supported (w : V m n) (b : Bool) (i : ℕ) :
    supportedBelow (n + 2) ((blockEncode m n b w).coeff i) := by
  intro j hj
  exact gridEncode_coeff_zero _ i j (Or.inr hj)

def PrefixSupported (w : V m n) (r : ℕ) : Prop :=
  ∀ b i j, r ≤ i.val → w (b, (i, j)) = 0

def SuffixSupported (w : V m n) (r : ℕ) : Prop :=
  ∀ b i j, i.val < r → w (b, (i, j)) = 0

theorem row_zero (w : V m n) (b : Bool) (i : ℕ)
    (h : ∀ (k : Fin (m + 2)) (j : Fin (n + 2)), k.val = i → w (b, (k, j)) = 0) :
    (blockEncode m n b w).coeff i = 0 := by
  apply Polynomial.ext
  intro j
  by_cases hi : i < m + 2
  · by_cases hj : j < n + 2
    · exact (blockEncode_coeff w b ⟨i, hi⟩ ⟨j, hj⟩).trans (h _ _ rfl)
    · simpa using gridEncode_coeff_zero (fun k l => w (b, (k, l))) i j (Or.inr (by omega))
  · simpa using gridEncode_coeff_zero (fun k l => w (b, (k, l))) i j (Or.inl (by omega))

theorem prefix_row_zero (w : V m n) {r i : ℕ} (hw : PrefixSupported w r) (hi : r ≤ i) :
    rowA w i = 0 ∧ rowB w i = 0 := by
  constructor
  · exact row_zero w false i (fun k j hk => hw false k j (by omega))
  · exact row_zero w true i (fun k j hk => hw true k j (by omega))

theorem suffix_row_zero (w : V m n) {r i : ℕ} (hw : SuffixSupported w r) (hi : i < r) :
    rowA w i = 0 ∧ rowB w i = 0 := by
  constructor
  · exact row_zero w false i (fun k j hk => hw false k j (by omega))
  · exact row_zero w true i (fun k j hk => hw true k j (by omega))

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

theorem forward_recurrence (w : V m n) (hw : (HZ m n).mulVec w = 0)
    (j : ℕ) (hj : j + 2 ≤ m + 1) :
    StripLocal.t * rowA w j + rowA w (j + 2) + rowB w j +
      rowB w (j + 1) + StripLocal.s * rowB w (j + 2) = 0 := by
  have h := x_cycle_coeff w hw (j + 2) (by omega) hj
  rw [fullSyndrome_apply, syndrome_coeff_add_two] at h
  exact h

/-- Multiplication by a degree-two factor removes two available support positions. -/
theorem factor_support {n : ℕ} (f p : P) (hf : f ≠ 0) (hd : f.natDegree = 2)
    (hp : supportedBelow (n + 2) (f * p)) : supportedBelow n p := by
  by_cases hz : p = 0
  · intro j _
    simp [hz]
  have hdeg : (f * p).natDegree < n + 2 :=
    (natDegree_lt_iff_degree_lt (mul_ne_zero hf hz)).mpr
      ((degree_lt_iff_coeff_zero _ _).mpr hp)
  rw [natDegree_mul hf hz, hd] at hdeg
  intro j hj
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem t_natDegree : StripLocal.t.natDegree = 2 := by
  have h : (X : P).natDegree < ((X : P) ^ 2).natDegree := by simp
  rw [StripLocal.t, natDegree_add_eq_right_of_natDegree_lt h]
  simp

theorem prefix_last_relation (w : V m n) {r : ℕ} (hr : r + 1 ≤ m)
    (hc : (HZ m n).mulVec w = 0) (hs : PrefixSupported w (r + 1)) :
    rowB w r = StripLocal.t * rowA w r := by
  have h := forward_recurrence w hc r (by omega)
  obtain ⟨ha₁, hb₁⟩ := prefix_row_zero w hs (by omega : r + 1 ≤ r + 1)
  obtain ⟨ha₂, hb₂⟩ := prefix_row_zero w hs (by omega : r + 1 ≤ r + 2)
  rw [ha₂, hb₁, hb₂] at h
  simp only [add_zero, mul_zero] at h
  simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h

theorem prefix_last_supported (w : V m n) {r : ℕ} (hr : r + 1 ≤ m)
    (hc : (HZ m n).mulVec w = 0) (hs : PrefixSupported w (r + 1)) :
    supportedBelow n (rowA w r) := by
  apply factor_support StripLocal.t _ StripLocal.t_ne_zero t_natDegree
  rw [← prefix_last_relation w hr hc hs]
  exact row_supported w true r

/-- A polynomial combination of the X rows with one fixed first anchor coordinate. -/
def xPacket (m n k : ℕ) (h : P) : V m n :=
  xSynthesis m n (fun a => if a.1.val = k then h.coeff a.2.val else 0)

theorem packet_entry {k : ℕ} (hk : k < m + 4) (h : P) (hh : supportedBelow n h) (i : ℕ) :
    entry (pack (m + 4) n
      (xAnchorCoordinates m n (fun a => if a.1.val = k then h.coeff a.2.val else 0))) i =
        if i = k then h else 0 := by
  unfold entry
  split
  · rename_i hi
    apply Polynomial.ext
    intro j
    by_cases hj : j < n
    · rw [pack_coeff _ ⟨i, hi⟩ ⟨j, hj⟩]
      simp only [RectangleFamily.xAnchorCoordinates, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      split_ifs <;> simp
    · rw [pack_supportedBelow _ ⟨i, hi⟩ j (by omega)]
      split_ifs <;> simp [hh j (by omega)]
  · rename_i hi
    have he : i ≠ k := by omega
    simp [he]

theorem xPacket_apply {k : ℕ} (hk : k < m + 4) (h : P) (hh : supportedBelow n h)
    (i : Fin (m + 2)) (j : Fin (n + 2)) :
    xPacket m n k h (false, (i, j)) =
      ((if i.val = k then h else 0) + (if i.val + 1 = k then h else 0) +
        StripLocal.s * (if i.val + 2 = k then h else 0)).coeff j.val ∧
    xPacket m n k h (true, (i, j)) =
      (StripLocal.t * (if i.val = k then h else 0) +
        (if i.val + 2 = k then h else 0)).coeff j.val := by
  constructor
  · change (entry (pack (m + 4) n (xAnchorCoordinates m n
        (fun a => if a.1.val = k then h.coeff a.2.val else 0))) i.val +
      entry (pack (m + 4) n (xAnchorCoordinates m n
        (fun a => if a.1.val = k then h.coeff a.2.val else 0))) (i.val + 1) +
      (X : P) ^ 2 * entry (pack (m + 4) n (xAnchorCoordinates m n
        (fun a => if a.1.val = k then h.coeff a.2.val else 0))) (i.val + 2)).coeff j.val = _
    simp only [packet_entry hk h hh, StripLocal.s]
  · change (((X : P) + X ^ 2) * entry (pack (m + 4) n (xAnchorCoordinates m n
        (fun a => if a.1.val = k then h.coeff a.2.val else 0))) i.val +
      entry (pack (m + 4) n (xAnchorCoordinates m n
        (fun a => if a.1.val = k then h.coeff a.2.val else 0))) (i.val + 2)).coeff j.val = _
    simp only [packet_entry hk h hh, StripLocal.t]

theorem xPacket_mem (m n k : ℕ) (h : P) : xPacket m n k h ∈ SX m n := by
  rw [SX, ← xSynthesis_eq]
  exact ⟨_, rfl⟩

theorem xPacket_cycle (m n k : ℕ) (h : P) : (HZ m n).mulVec (xPacket m n k h) = 0 :=
  x_mem_zOrthogonal m n (xPacket_mem m n k h)

/-- A cycle supported away from the right boundary is an X stabilizer. -/
theorem prefix_fill (r : ℕ) (hr : r ≤ m) (w : V m n)
    (hc : (HZ m n).mulVec w = 0) (hs : PrefixSupported w r) : w ∈ SX m n := by
  induction r generalizing w with
  | zero =>
    have hz : w = 0 := by
      funext q
      exact hs q.1 q.2.1 q.2.2 (Nat.zero_le _)
    rw [hz]
    exact (SX m n).zero_mem
  | succ r ih =>
    have hh := prefix_last_supported w hr hc hs
    let p := xPacket m n r (rowA w r)
    have hp : p ∈ SX m n := xPacket_mem m n r (rowA w r)
    have hpc : (HZ m n).mulVec p = 0 := xPacket_cycle m n r (rowA w r)
    have hc' : (HZ m n).mulVec (w - p) = 0 := by
      rw [Matrix.mulVec_sub, hc, hpc, sub_self]
    have hs' : PrefixSupported (w - p) r := by
      intro b i j hi
      have he := xPacket_apply (m := m) (n := n) (by omega : r < m + 4) (rowA w r) hh i j
      by_cases hir : i.val = r
      · have hne₁ : i.val + 1 ≠ r := by omega
        have hne₂ : i.val + 2 ≠ r := by omega
        simp only [if_pos hir, if_neg hne₁, if_neg hne₂, mul_zero, add_zero] at he
        have hrel := prefix_last_relation w hr hc hs
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [show p (false, (i, j)) = (rowA w r).coeff j.val from he.1]
          rw [← hir, rowA_coeff, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [show p (true, (i, j)) = (StripLocal.t * rowA w r).coeff j.val from he.2,
            ← hrel, ← hir, rowB_coeff, sub_self]
      · have hne₁ : i.val + 1 ≠ r := by omega
        have hne₂ : i.val + 2 ≠ r := by omega
        simp only [if_neg hir, if_neg hne₁, if_neg hne₂, mul_zero, add_zero, coeff_zero] at he
        have hw := hs b i j (by omega)
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [hw, show p (false, (i, j)) = 0 from he.1, sub_self]
        · change w (true, (i, j)) - p (true, (i, j)) = 0
          rw [hw, show p (true, (i, j)) = 0 from he.2, sub_self]
    have hmem := ih (by omega) (w - p) hc' hs'
    have hadd := (SX m n).add_mem hmem hp
    simpa only [sub_add_cancel] using hadd


theorem suffix_first_relation (w : V m n) {r : ℕ} (hr : 2 ≤ r) (hr' : r < m + 2)
    (hc : (HZ m n).mulVec w = 0) (hs : SuffixSupported w r) :
    rowA w r = StripLocal.s * rowB w r := by
  have h := forward_recurrence w hc (r - 2) (by omega)
  obtain ⟨ha₀, hb₀⟩ := suffix_row_zero w hs (by omega : r - 2 < r)
  obtain ⟨ha₁, hb₁⟩ := suffix_row_zero w hs (by omega : r - 1 < r)
  have he₂ : r - 2 + 2 = r := by omega
  have he₁ : r - 2 + 1 = r - 1 := by omega
  rw [he₂, he₁, ha₀, hb₀, hb₁] at h
  simpa only [zero_add, add_zero, mul_zero, CharTwo.neg_eq] using
    eq_neg_of_add_eq_zero_left h

theorem suffix_first_supported (w : V m n) {r : ℕ} (hr : 2 ≤ r) (hr' : r < m + 2)
    (hc : (HZ m n).mulVec w = 0) (hs : SuffixSupported w r) :
    supportedBelow n (rowB w r) := by
  apply factor_support StripLocal.s _ (pow_ne_zero 2 Polynomial.X_ne_zero)
    (Polynomial.natDegree_X_pow 2)
  rw [← suffix_first_relation w hr hr' hc hs]
  exact row_supported w false r

/-- A cycle supported away from the left boundary is an X stabilizer. -/
theorem suffix_fill (r : ℕ) (hr : r ≤ m) (w : V m n)
    (hc : (HZ m n).mulVec w = 0) (hs : SuffixSupported w (m + 2 - r)) :
    w ∈ SX m n := by
  induction r generalizing w with
  | zero =>
    have hz : w = 0 := by
      funext q
      exact hs q.1 q.2.1 q.2.2 (by have := q.2.1.isLt; omega)
    rw [hz]
    exact (SX m n).zero_mem
  | succ r ih =>
    let k := m + 2 - (r + 1)
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hk' : k < m + 2 := by dsimp [k]; omega
    have hh := suffix_first_supported w hk hk' hc hs
    let p := xPacket m n (k + 2) (rowB w k)
    have hp : p ∈ SX m n := xPacket_mem m n (k + 2) (rowB w k)
    have hpc : (HZ m n).mulVec p = 0 := xPacket_cycle m n (k + 2) (rowB w k)
    have hc' : (HZ m n).mulVec (w - p) = 0 := by
      rw [Matrix.mulVec_sub, hc, hpc, sub_self]
    have hs' : SuffixSupported (w - p) (m + 2 - r) := by
      intro b i j hi
      have hik : i.val ≤ k := by dsimp [k]; omega
      have he := xPacket_apply (m := m) (n := n) (by omega : k + 2 < m + 4)
        (rowB w k) hh i j
      have hne₀ : i.val ≠ k + 2 := by omega
      have hne₁ : i.val + 1 ≠ k + 2 := by omega
      by_cases hir : i.val = k
      · have he₂ : i.val + 2 = k + 2 := by omega
        simp only [if_neg hne₀, if_neg hne₁, if_pos he₂, mul_zero,
          zero_add] at he
        have hrel := suffix_first_relation w hk hk' hc hs
        cases b
        · change w (false, (i, j)) - p (false, (i, j)) = 0
          rw [show p (false, (i, j)) = (StripLocal.s * rowB w k).coeff j.val from he.1,
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
    have hadd := (SX m n).add_mem hmem hp
    simpa only [sub_add_cancel] using hadd

end
end QldpcVerification.Planar.RectangleFamilyPeeling
