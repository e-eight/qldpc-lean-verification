import QldpcVerification.Input.Homological
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Analytic exclusion of logicals of weight at most two

The hypotheses concern columns, not enumerated logical supports. Equal columns
may occur: their two-site vector must be a stabilizer. No independence of check
rows, positive code dimension, or existence of a logical is required.
-/

namespace QldpcVerification.Planar.SmallSupport

open Matrix

variable {Q R : Type*} [Fintype Q] [DecidableEq Q]

/-- Physical nonzero coordinates, whose cardinality is Mathlib's Hamming norm. -/
def support (x : Q → ZMod 2) : Finset Q :=
  Finset.univ.filter fun q => x q ≠ 0

theorem card_support (x : Q → ZMod 2) : (support x).card = hammingNorm x := rfl

theorem eq_indicator_support (x : Q → ZMod 2) :
    x = fun q => if q ∈ support x then 1 else 0 := by
  funext q
  have hbit : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  by_cases hq : x q = 0
  · simp [support, hq]
  · simp [support, hq, hbit (x q) hq]

/-- Singleton and pair classification uses support cardinality, not a search. -/
theorem classify_weight_le_two (x : Q → ZMod 2) (hx : hammingNorm x ≤ 2) :
    x = 0 ∨ (∃ i, x = Pi.single i 1) ∨
      ∃ i j, i ≠ j ∧ x = Pi.single i 1 + Pi.single j 1 := by
  have hc : (support x).card ≤ 2 := by simpa [card_support] using hx
  have cases : (support x).card = 0 ∨ (support x).card = 1 ∨
      (support x).card = 2 := by omega
  rcases cases with h0 | h1 | h2
  · left
    apply hammingNorm_eq_zero.mp
    exact (card_support x).symm.trans h0
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    right; left
    refine ⟨i, (eq_indicator_support x).trans ?_⟩
    funext q
    by_cases hq : q = i
    · subst q
      simp [hi]
    · simp [hi, Pi.single_apply, hq, Ne.symm hq]
  · obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp h2
    right; right
    refine ⟨i, j, hij, (eq_indicator_support x).trans ?_⟩
    funext q
    by_cases hi : q = i
    · subst q
      simp [hs, Pi.single_apply, hij, Ne.symm hij]
    · by_cases hj : q = j
      · subst q
        simp [hs, Pi.single_apply, hij, Ne.symm hij]
      · simp [hs, Pi.single_apply, hi, hj, Ne.symm hi, Ne.symm hj]

/-- Every low-weight cycle is in `B` if nonzero columns have only trivial
two-site collisions. In CSS applications `B` is the opposite check row space. -/
theorem small_cycle_mem (H : Matrix R Q (ZMod 2))
    (B : Submodule (ZMod 2) (Q → ZMod 2))
    (nonzero : ∀ i, H.col i ≠ 0)
    (collisions : ∀ i j, i ≠ j → H.col i = H.col j →
      Pi.single i 1 + Pi.single j 1 ∈ B)
    (x : Q → ZMod 2) (cycle : H.mulVec x = 0) (small : hammingNorm x ≤ 2) :
    x ∈ B := by
  rcases classify_weight_le_two x small with rfl | ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · exact B.zero_mem
  · exact False.elim (nonzero i (by simpa only [Matrix.mulVec_single_one] using cycle))
  · apply collisions i j hij
    rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at cycle
    funext r
    have hr : H.col i r + H.col j r = 0 := congrFun cycle r
    have cancel : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact cancel _ _ hr

/-- A nontrivial cycle has Hamming weight at least three. -/
theorem weight_ge_three (H : Matrix R Q (ZMod 2))
    (B : Submodule (ZMod 2) (Q → ZMod 2))
    (nonzero : ∀ i, H.col i ≠ 0)
    (collisions : ∀ i j, i ≠ j → H.col i = H.col j →
      Pi.single i 1 + Pi.single j 1 ∈ B)
    (x : Q → ZMod 2) (cycle : H.mulVec x = 0) (nontrivial : x ∉ B) :
    3 ≤ hammingNorm x := by
  by_contra h
  exact nontrivial (small_cycle_mem H B nonzero collisions x cycle (by omega))

open Input Quantum Quantum.Stabilizer.Homological

variable {n mX mZ : ℕ} (C : CSSCode n mX mZ)

/-- Column hypotheses for one sector, with the stabilizer space explicit. -/
structure ColumnCriterion (H : Matrix R Q (ZMod 2))
    (B : Submodule (ZMod 2) (Q → ZMod 2)) : Prop where
  nonzero : ∀ i, H.col i ≠ 0
  collisions : ∀ i j, i ≠ j → H.col i = H.col j →
    Pi.single i 1 + Pi.single j 1 ∈ B

theorem x_lower (h : ColumnCriterion C.HZ C.xStab)
    (x : Vec n) (hx : C.IsXLogical x) : 3 ≤ hammingNorm x :=
  weight_ge_three C.HZ C.xStab h.nonzero h.collisions x hx.1 hx.2

theorem z_lower (h : ColumnCriterion C.HX C.zStab)
    (z : Vec n) (hz : C.IsZLogical z) : 3 ≤ hammingNorm z :=
  weight_ge_three C.HX C.zStab h.nonzero h.collisions z hz.1 hz.2

/-- The same exact hypotheses bound mixed Pauli logicals via QECLean's bridge. -/
theorem pauli_lower (hx : ColumnCriterion C.HZ C.xStab)
    (hz : ColumnCriterion C.HX C.zStab)
    (g : NQubitPauliGroupElement C.homological.numQubits)
    (hg : StabilizerGroup.IsNontrivialLogicalOperator g
      C.homological.homologicalStabilizerGroup) :
    3 ≤ NQubitPauliGroupElement.weight g :=
  HomologicalCode.chainWeight_lower_bound_transfers C.homological 3
    (fun v hv hb => x_lower C hx v ((C.x_logical_iff v).mpr ⟨hv, hb⟩))
    (fun v hv hb => z_lower C hz v ((C.z_logical_iff v).mpr ⟨hv, hb⟩)) g hg

/-!
## Adapter obligations for the literal 722 code (not discharged here)

Use `C : Input.CSSCode 722 357 357` with the recognized ordered matrices
of analytical/notes/algebra.md, Proposition 4; write A(i,j)=19*i+j and
B(i,j)=361+19*i+j for 0 ≤ i,j ≤ 18.

* For `ColumnCriterion C.HZ C.xStab`, show every HZ column is nonzero.
  Distinct equal columns must, up to exchange, be A(18,j), B(18,j-2),
  2 ≤ j ≤ 18. Their two-site vector is the HX row X_(18,j-2).
* For `ColumnCriterion C.HX C.zStab`, show every HX column is nonzero.
  Distinct equal columns must, up to exchange, be A(i,18), B(i+2,18),
  0 ≤ i ≤ 16. Their two-site vector is the HZ row Z_(i+2,20).

Each row belongs to its span by `Submodule.subset_span ⟨rowIndex, rfl⟩`.
Recognizing the literal matrices and proving these symbolic column
classifications are separate obligations; no 722 bound is asserted here.
-/

end QldpcVerification.Planar.SmallSupport
