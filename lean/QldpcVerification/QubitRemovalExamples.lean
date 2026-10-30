import QldpcVerification.QubitRemoval

/-! Kernel-evaluated minima of actual cycles modulo actual matrix row spaces. -/
namespace QldpcVerification.QubitRemoval.Examples

open Matrix Module Input

set_option maxRecDepth 10000

/-- Finite coefficient form of the existing X-logical predicate; no surrogate distance. -/
private theorem x_finite {n a b : ℕ} (C : CSSCode n a b) (x : Vec n) :
    C.IsXLogical x ↔ C.HZ.mulVec x = 0 ∧ ¬ ∃ u : Vec a, C.HX.transpose.mulVec u = x := by
  have hr : LinearMap.range C.HX.transpose.mulVecLin = C.xStab := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [CSSCode.IsXLogical, ← hr]
  rfl

private theorem z_finite {n a b : ℕ} (C : CSSCode n a b) (z : Vec n) :
    C.IsZLogical z ↔ C.HX.mulVec z = 0 ∧ ¬ ∃ u : Vec b, C.HZ.transpose.mulVec u = z := by
  have hr : LinearMap.range C.HZ.transpose.mulVecLin = C.zStab := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [CSSCode.IsZLogical, ← hr]
  rfl

private theorem distX_finite {n a b : ℕ} (C : CSSCode n a b) (D : ℕ) :
    C.DistX D ↔
      (∃ x, (C.HZ.mulVec x = 0 ∧ ¬ ∃ u : Vec a, C.HX.transpose.mulVec u = x) ∧
        hammingNorm x = D) ∧
      ∀ x, (C.HZ.mulVec x = 0 ∧ ¬ ∃ u : Vec a, C.HX.transpose.mulVec u = x) →
        D ≤ hammingNorm x := by
  simp only [CSSCode.DistX, x_finite]

private theorem distZ_finite {n a b : ℕ} (C : CSSCode n a b) (D : ℕ) :
    C.DistZ D ↔
      (∃ z, (C.HX.mulVec z = 0 ∧ ¬ ∃ u : Vec b, C.HZ.transpose.mulVec u = z) ∧
        hammingNorm z = D) ∧
      ∀ z, (C.HX.mulVec z = 0 ∧ ¬ ∃ u : Vec b, C.HZ.transpose.mulVec u = z) →
        D ≤ hammingNorm z := by
  simp only [CSSCode.DistZ, z_finite]

private theorem independent_rows_rank {n a : ℕ} (H : Matrix (Fin a) (Fin n) (ZMod 2))
    (h : ∀ c : Vec a, (∑ i, c i • H i) = 0 → ∀ i, c i = 0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) = a := by
  simpa using finrank_span_eq_card (Fintype.linearIndependent_iff.mpr h)

/-- The retained [[4,2,2]] code, in both preserving and increasing examples. -/
def four : CSSCode 4 1 1 where
  HX := fun _ => ![1, 1, 1, 1]
  HZ := fun _ => ![1, 1, 1, 1]
  comm := by decide +kernel

def singleFan : Vec 4 := ![1, 0, 0, 0]
def doubleFan : Vec 4 := ![1, 1, 0, 0]
abbrev preserving := old four singleFan
abbrev increasing := old four doubleFan

theorem four_ranks : finrank (ZMod 2) four.xStab = 1 ∧
    finrank (ZMod 2) four.zStab = 1 := by
  constructor <;> apply independent_rows_rank <;> decide +kernel

theorem four_distances : four.DistX 2 ∧ four.DistZ 2 := by
  constructor
  · rw [distX_finite]; decide +kernel
  · rw [distZ_finite]; decide +kernel

theorem preserving_ranks : finrank (ZMod 2) preserving.xStab = 2 ∧
    finrank (ZMod 2) preserving.zStab = 1 := by
  rw [rankX, rankZ, four_ranks.1, four_ranks.2]
  exact ⟨rfl, rfl⟩

theorem preserving_distances : preserving.DistX 2 ∧ preserving.DistZ 2 := by
  constructor
  · rw [distX_finite]; decide +kernel
  · rw [distZ_finite]; decide +kernel

theorem preserving_parameters :
    (5 - finrank (ZMod 2) preserving.xStab - finrank (ZMod 2) preserving.zStab = 2) ∧
      preserving.DistX 2 ∧ preserving.DistZ 2 := by
  rw [preserving_ranks.1, preserving_ranks.2]
  exact ⟨rfl, preserving_distances⟩

/-- Deletion can strictly increase X distance, with no change on Z. -/
theorem increasing_distances : increasing.DistX 1 ∧ increasing.DistZ 2 := by
  constructor
  · rw [distX_finite]; decide +kernel
  · rw [distZ_finite]; decide +kernel

/-- Empty retained X checks and two independent retained Z checks. -/
def three : CSSCode 3 0 2 where
  HX := Fin.elim0
  HZ := ![![1, 1, 0], ![0, 0, 1]]
  comm := by decide +kernel

def tripleFan : Vec 3 := ![1, 1, 1]
abbrev losing := old three tripleFan

theorem three_ranks : finrank (ZMod 2) three.xStab = 0 ∧
    finrank (ZMod 2) three.zStab = 2 := by
  constructor <;> apply independent_rows_rank <;> decide +kernel

theorem three_distances : three.DistX 2 ∧ three.DistZ 1 := by
  constructor
  · rw [distX_finite]; decide +kernel
  · rw [distZ_finite]; decide +kernel

theorem losing_ranks : finrank (ZMod 2) losing.xStab = 1 ∧
    finrank (ZMod 2) losing.zStab = 2 := by
  rw [rankX, rankZ, three_ranks.1, three_ranks.2]
  exact ⟨rfl, rfl⟩

theorem losing_distances : losing.DistX 2 ∧ losing.DistZ 2 := by
  constructor
  · rw [distX_finite]; decide +kernel
  · rw [distZ_finite]; decide +kernel

theorem losing_parameters :
    (4 - finrank (ZMod 2) losing.xStab - finrank (ZMod 2) losing.zStab = 1) ∧
      losing.DistX 2 ∧ losing.DistZ 2 := by
  rw [losing_ranks.1, losing_ranks.2]
  exact ⟨rfl, losing_distances⟩

/-- Literal old checks agree with XXXX, ZZII, IIZZ in that order. -/
theorem losing_matrices : losing.HX = ![![1, 1, 1, 1]] ∧
    losing.HZ = ![![1, 1, 0, 0], ![0, 0, 1, 1]] := by
  decide +kernel

/-- The preserving result can also be obtained through the general lifting criteria. -/
theorem preserving_via_criteria : preserving.DistX 2 ∧ preserving.DistZ 2 := by
  constructor
  · apply (distX_preserved_iff four singleFan four_distances.1).mpr
    simp only [x_finite]
    decide +kernel
  · apply distZ_preserved four singleFan four_distances.2
    refine ⟨![0, 0, 1, 1], ?_, ?_, ?_⟩
    · rw [z_finite]; decide +kernel
    · decide +kernel
    · decide +kernel

/-- The one-unit Z loss is certified by the exact odd-minimum characterization. -/
theorem losing_via_criterion : losing.DistZ 2 := by
  apply (distZ_loss_iff three tripleFan three_distances.2).mpr
  simp only [z_finite]
  decide +kernel

/-- Even in a preserving case the canonical Z lift can cost an extra bit. -/
theorem preserving_canonical_lift_grows :
    four.IsZLogical ![1, 1, 0, 0] ∧
      hammingNorm (![1, 1, 0, 0] : Vec 4) = 2 ∧
      hammingNorm (liftZ singleFan ![1, 1, 0, 0]) = 3 := by
  rw [z_finite]
  decide +kernel

end QldpcVerification.QubitRemoval.Examples
