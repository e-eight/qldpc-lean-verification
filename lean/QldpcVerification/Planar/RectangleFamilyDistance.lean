import QldpcVerification.Planar.RectangleFamilyZGap
import QldpcVerification.Planar.StripFamilyRunRecurrence
import QldpcVerification.Transport

/-! Family distance bounds from physical peeling and polynomial run accounting. -/
namespace QldpcVerification.Planar.RectangleFamilyDistance

open Polynomial RectangleFamily RectangleFamilySyndrome RectangleFamilyPeeling
open StripLocal

noncomputable section
variable {m n : ℕ}

theorem wt_eq_sum_fin (p : StripLocal.P) (N : ℕ)
    (hp : ∀ j, N ≤ j → p.coeff j = 0) :
    wt p = ∑ j : Fin N, if p.coeff j.val ≠ 0 then 1 else 0 := by
  classical
  have hs : p.support = (Finset.range N).filter (fun j => p.coeff j ≠ 0) := by
    ext j
    simp only [Polynomial.mem_support_iff, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hj
      exact ⟨by by_contra hn; exact hj (hp j (by omega)), hj⟩
    · exact fun hj => hj.2
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if p.coeff j ≠ 0 then 1 else 0) N]
  simp only [wt, hs, Finset.card_filter]

theorem block_slice_weight (w : V m n) (b : Bool) (i : Fin (m + 2)) :
    wt ((blockEncode m n b w).coeff i.val) =
      ∑ j : Fin (n + 2), if w (b, (i, j)) ≠ 0 then 1 else 0 := by
  rw [wt_eq_sum_fin _ (n + 2) (row_supported w b i.val)]
  simp only [blockEncode_coeff]

theorem hammingNorm_bool_prod {I J : Type*} [Fintype I] [Fintype J]
    (w : Bool × (I × J) → ZMod 2) :
    hammingNorm w =
      (∑ i : I, ∑ j : J, if w (false, (i, j)) ≠ 0 then 1 else 0) +
      (∑ i : I, ∑ j : J, if w (true, (i, j)) ≠ 0 then 1 else 0) := by
  classical
  simp only [hammingNorm, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

theorem row_weight (w : V m n) :
    (∑ i ∈ Finset.range (m + 2), pairWt (rowA w i) (rowB w i)) = hammingNorm w := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => pairWt (rowA w i) (rowB w i)) (m + 2)]
  rw [hammingNorm_bool_prod, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change wt ((blockEncode m n false w).coeff i.val) +
    wt ((blockEncode m n true w).coeff i.val) = _
  rw [block_slice_weight, block_slice_weight]

/-- The X-sector bound grows with the first side length, uniformly in the second. -/
theorem x_lower (w : V m n) (hc : (HZ m n).mulVec w = 0) (hb : w ∉ SX m n) :
    m ≤ hammingNorm w := by
  cases m with
  | zero => exact Nat.zero_le _
  | succ m =>
    have hf : StripFamilyRecurrence.Forward m (rowA w) (rowB w) := by
      intro i hi hi'
      have h := forward_recurrence w hc (i - 2) (by omega)
      have h₂ : i - 2 + 2 = i := by omega
      have h₁ : i - 2 + 1 = i - 1 := by omega
      rw [h₂, h₁] at h
      have he : rowA w i + (StripLocal.t * rowA w (i - 2) +
          rowB w (i - 1) + rowB w (i - 2) + StripLocal.s * rowB w i) = 0 := by
        simpa only [add_assoc, add_comm, add_left_comm] using h
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he
    have ha : StripFamilyRecurrence.Adjacent m (rowA w) (rowB w) := by
      intro i hi
      exact RectangleFamilyGap.x_adjacent w hc hb i (by omega)
    have h := StripFamilyRunRecurrence.forward_weight_ge_length_sub_two (rowA w) (rowB w) hf ha
    simpa only [row_weight, Nat.succ_eq_add_one, Nat.add_assoc] using h


theorem column_weight (w : V m n) :
    (∑ i ∈ Finset.range (n + 2), pairWt (RectangleFamilyZGap.columnA w i)
      (RectangleFamilyZGap.columnB w i)) = hammingNorm w := by
  change (∑ i ∈ Finset.range (n + 2),
    pairWt (rowA (RectangleFamilyZPeeling.view m n w) i)
      (rowB (RectangleFamilyZPeeling.view m n w) i)) = hammingNorm w
  rw [row_weight, RectangleFamilyZPeeling.view_weight]

/-- The Z bound uses its separately proved reflected-column recurrence. -/
theorem z_lower (w : V m n) (hc : (HX m n).mulVec w = 0)
    (hb : w ∉ LinearMap.range (HZ m n).transpose.mulVecLin) :
    n ≤ hammingNorm w := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hf : StripFamilyRecurrence.Backward n
        (RectangleFamilyZGap.columnA w) (RectangleFamilyZGap.columnB w) := by
      intro i hi hi'
      have h := RectangleFamilyZGap.z_recurrence w hc (i - 2) (by omega)
      have h₂ : i - 2 + 2 = i := by omega
      have h₁ : i - 2 + 1 = i - 1 := by omega
      rw [h₂, h₁] at h
      have he : StripLocal.t * RectangleFamilyZGap.columnB w i +
          (RectangleFamilyZGap.columnA w i +
            StripLocal.s * RectangleFamilyZGap.columnA w (i - 1) +
            StripLocal.s * RectangleFamilyZGap.columnA w (i - 2) +
            RectangleFamilyZGap.columnB w (i - 2)) = 0 := by
        simpa only [add_assoc, add_comm, add_left_comm] using h
      simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left he
    have ha : StripFamilyRecurrence.Adjacent n
        (RectangleFamilyZGap.columnA w) (RectangleFamilyZGap.columnB w) := by
      intro i hi
      exact RectangleFamilyZGap.z_adjacent w hc hb i (by omega)
    have h := StripFamilyRunRecurrence.backward_weight_ge_length_sub_two
      (RectangleFamilyZGap.columnA w) (RectangleFamilyZGap.columnB w) hf ha
    simpa only [column_weight, Nat.succ_eq_add_one, Nat.add_assoc] using h

end
end QldpcVerification.Planar.RectangleFamilyDistance

namespace QldpcVerification.Planar.RectangleFamily

open Input

/-- The canonical finite-index X rows pull back to the original rectangle rows. -/
theorem x_rows (m n : ℕ) (i : Fin ((m + 4) * n)) :
    pull (qubits m n) ((code m n).HX i) = HX m n ((xRows m n).symm i) := by
  ext q
  simp [pull, code]

theorem z_rows (m n : ℕ) (i : Fin (m * (n + 4))) :
    pull (qubits m n) ((code m n).HZ i) = HZ m n ((zRows m n).symm i) := by
  ext q
  simp [pull, code]

theorem x_logical_iff (m n : ℕ) (x : Vec (2 * ((m + 2) * (n + 2)))) :
    (code m n).IsXLogical x ↔
      (HZ m n).mulVec (pull (qubits m n) x) = 0 ∧
        pull (qubits m n) x ∉ SX m n := by
  change ((code m n).HZ.mulVec x = 0 ∧
    x ∉ Submodule.span F2 (Set.range (code m n).HX)) ↔ _
  rw [kernel_pull_iff (qubits m n) (code m n).HZ (HZ m n)
    (zRows m n).symm (zRows m n).symm.surjective (z_rows m n) x]
  have hs : SX m n = Submodule.span F2 (Set.range (HX m n)) :=
    Matrix.range_mulVecLin (HX m n).transpose
  rw [hs]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff (qubits m n) (code m n).HX (HX m n)
      (xRows m n).symm (xRows m n).symm.surjective (x_rows m n) x)).symm

/-- X logical operators in the QECLean-backed code have weight at least `m`. -/
theorem x_lower (m n : ℕ) (x : Vec (2 * ((m + 2) * (n + 2))))
    (hx : (code m n).IsXLogical x) : m ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (x_logical_iff m n x).mp hx
  simpa only [pull_weight] using RectangleFamilyDistance.x_lower
    (pull (qubits m n) x) hc hb


theorem z_logical_iff (m n : ℕ) (z : Vec (2 * ((m + 2) * (n + 2)))) :
    (code m n).IsZLogical z ↔
      (HX m n).mulVec (pull (qubits m n) z) = 0 ∧
        pull (qubits m n) z ∉ LinearMap.range (HZ m n).transpose.mulVecLin := by
  change ((code m n).HX.mulVec z = 0 ∧
    z ∉ Submodule.span F2 (Set.range (code m n).HZ)) ↔ _
  rw [kernel_pull_iff (qubits m n) (code m n).HX (HX m n)
    (xRows m n).symm (xRows m n).symm.surjective (x_rows m n) z]
  have hs : LinearMap.range (HZ m n).transpose.mulVecLin =
      Submodule.span F2 (Set.range (HZ m n)) :=
    Matrix.range_mulVecLin (HZ m n).transpose
  rw [hs]
  exact and_congr Iff.rfl (not_congr
    (rowspace_pull_iff (qubits m n) (code m n).HZ (HZ m n)
      (zRows m n).symm (zRows m n).symm.surjective (z_rows m n) z)).symm

theorem z_lower (m n : ℕ) (z : Vec (2 * ((m + 2) * (n + 2))))
    (hz : (code m n).IsZLogical z) : n ≤ hammingNorm z := by
  obtain ⟨hc, hb⟩ := (z_logical_iff m n z).mp hz
  simpa only [pull_weight] using RectangleFamilyDistance.z_lower
    (pull (qubits m n) z) hc hb

open Quantum Quantum.Stabilizer.Homological

/-- The sector bounds include every mixed Pauli logical in QECLean. -/
theorem pauli_lower (m n : ℕ)
    (g : NQubitPauliGroupElement (code m n).homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      (code m n).homological.homologicalStabilizerGroup) :
    min m n ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers (code m n).homological (min m n)
    (fun v hv hb => (Nat.min_le_left m n).trans
      (x_lower m n v (((code m n).x_logical_iff v).mpr ⟨hv, hb⟩)))
    (fun v hv hb => (Nat.min_le_right m n).trans
      (z_lower m n v (((code m n).z_logical_iff v).mpr ⟨hv, hb⟩))) g hg

/-- Uniform ranks, encoded dimension, and both CSS distance lower bounds. -/
theorem parameters_and_bounds (m n : ℕ) :
    Module.finrank F2 (code m n).xStab = (m + 4) * n ∧
    Module.finrank F2 (code m n).zStab = m * (n + 4) ∧
    2 * ((m + 2) * (n + 2)) - Module.finrank F2 (code m n).xStab -
      Module.finrank F2 (code m n).zStab = 8 ∧
    (∀ x, (code m n).IsXLogical x → m ≤ hammingNorm x) ∧
    (∀ z, (code m n).IsZLogical z → n ≤ hammingNorm z) :=
  ⟨rankX m n, rankZ m n, encoded_qubits m n, x_lower m n, z_lower m n⟩

end QldpcVerification.Planar.RectangleFamily
