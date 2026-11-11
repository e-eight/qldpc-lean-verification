import QldpcVerification.Rectangle722Submitted
import QldpcVerification.Input.LogicalWitness
import QldpcVerification.Input.SparseCertificates

/-!
Two supplied supports and a sparse Laurent-syndrome proof of a weight-20
nontrivial Z/Pauli witness. No support search, dense matrix evaluation, or
error enumeration. Pending external capped replay and independent reviews.
-/
namespace QldpcVerification.Rectangle722Witness

open Matrix Input Planar.Commutation
open Quantum Quantum.Stabilizer.Homological

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- Coefficient of a Laurent polynomial presented as a multiset of exponents.
Repeated terms add over F₂; negative coordinates are allowed. -/
def coefficient (s : Multiset Lattice) (p : Lattice) : F2 :=
  (s.map (fun t => if p = t then (1 : F2) else 0)).sum

@[simp] theorem coefficient_add (s t : Multiset Lattice) (p : Lattice) :
    coefficient (s + t) p = coefficient s p + coefficient t p := by
  simp [coefficient, Multiset.map_add]

/-- Adding two copies of any polynomial cancels every coefficient. -/
theorem coefficient_cancel (r c : Multiset Lattice) (p : Lattice) :
    coefficient (r + c + c) p = coefficient r p := by
  simp only [coefficient_add, add_assoc, ← two_mul]
  have htwo : (2 : F2) = 0 := by decide
  rw [htwo, zero_mul, add_zero]

/-- Full g*u + f*v contribution of one physical X impulse. -/
def xImpulse (q : Fin 722) : Multiset Lattice :=
  let w := Rectangle722.qubits.symm q
  let s := if w.1 then fShift else gShift
  {cell w.2 + s 0, cell w.2 + s 1, cell w.2 + s 2}

/-- Full bar(f)*u + bar(g)*v contribution of one physical Z impulse. -/
def zImpulse (q : Fin 722) : Multiset Lattice :=
  let w := Rectangle722.qubits.symm q
  let s := if w.1 then gShift else fShift
  {cell w.2 - s 0, cell w.2 - s 1, cell w.2 - s 2}

/-- Multiplication by the check polynomials is translation of each monomial. -/
def syndromeTerms (impulse : Fin 722 → Multiset Lattice) :
    List (Fin 722) → Multiset Lattice
  | [] => 0
  | q :: qs => impulse q + syndromeTerms impulse qs

/-- Sparse vector as a sum of coordinate impulses. -/
def vector : List (Fin 722) → Vec 722
  | [] => 0
  | q :: qs => Pi.single q 1 + vector qs

/-- Generic sparse dot-product bridge: only the supplied support is traversed. -/
theorem sparse_dot (v : Vec 722) (impulse : Fin 722 → Multiset Lattice)
    (p : Lattice) (h : ∀ q, v q = coefficient (impulse q) p)
    (s : List (Fin 722)) :
    v ⬝ᵥ vector s = coefficient (syndromeTerms impulse s) p := by
  induction s with
  | nil => simp [vector, syndromeTerms, coefficient]
  | cons q qs ih =>
    simp only [vector, syndromeTerms, dotProduct_add, dotProduct_single_one,
      coefficient_add, h, ih]

/-- Symbolic in the physical impulse and anchor. Three shifts, no board sweep. -/
theorem x_impulse_coefficient (q : Fin 722) (a : ZAnchor) :
    coefficient (xImpulse q) (zAnchor a) = HZ a (Rectangle722.qubits.symm q) := by
  unfold xImpulse
  generalize Rectangle722.qubits.symm q = w
  rcases w with ⟨b, i, j⟩
  cases b <;>
    simp only [Bool.false_eq_true, if_false, if_true, coefficient,
      Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, HZ, zBlock,
      Fin.sum_univ_succ, Fin.sum_univ_zero, fShift, gShift,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      atom, cell, zAnchor, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq] <;>
    split_ifs <;> first | omega | ring

theorem z_impulse_coefficient (q : Fin 722) (a : XAnchor) :
    coefficient (zImpulse q) (xAnchor a) = HX a (Rectangle722.qubits.symm q) := by
  unfold zImpulse
  generalize Rectangle722.qubits.symm q = w
  rcases w with ⟨b, i, j⟩
  cases b <;>
    simp only [Bool.false_eq_true, if_false, if_true, coefficient,
      Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, HX, xBlock,
      Fin.sum_univ_succ, Fin.sum_univ_zero, fShift, gShift,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons,
      atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk_sub_mk, Prod.mk.injEq] <;>
    split_ifs <;> first | omega | ring

theorem x_syndrome_coefficient (s : List (Fin 722)) (i : Fin 357) :
    Rectangle722.code.HZ.mulVec (vector s) i =
      coefficient (syndromeTerms xImpulse s) (zAnchor (Rectangle722.zRows.symm i)) := by
  exact sparse_dot (Rectangle722.code.HZ i) xImpulse
    (zAnchor (Rectangle722.zRows.symm i))
    (fun q => (x_impulse_coefficient q (Rectangle722.zRows.symm i)).symm) s

theorem z_syndrome_coefficient (s : List (Fin 722)) (i : Fin 357) :
    Rectangle722.code.HX.mulVec (vector s) i =
      coefficient (syndromeTerms zImpulse s) (xAnchor (Rectangle722.xRows.symm i)) := by
  exact sparse_dot (Rectangle722.code.HX i) zImpulse
    (xAnchor (Rectangle722.xRows.symm i))
    (fun q => (z_impulse_coefficient q (Rectangle722.xRows.symm i)).symm) s

-- BEGIN FIXED WITNESS DATA

def xSupport : List (Fin 722) :=
  [65, 103, 104, 105, 142, 162, 199, 219, 220, 332, 390, 407, 426, 504, 541, 560, 561, 579, 598, 617, 619, 636, 655]

def xResidual : Multiset Lattice :=
  {(1, 12), (19, 10), (19, 11)}

def xCancellation : Multiset Lattice :=
  {(2, 10), (3, 8), (3, 10), (4, 8), (5, 8), (5, 9), (5, 10), (7, 9), (7, 10), (7, 11), (7, 12), (8, 10), (9, 10), (9, 11), (10, 9), (10, 11), (10, 12), (11, 9), (11, 10), (11, 11), (12, 9), (12, 10), (12, 11), (13, 9), (13, 11), (13, 12), (13, 13), (14, 9), (14, 11), (15, 9), (15, 11), (16, 9), (17, 9)}

def zSupport : List (Fin 722) :=
  [46, 47, 61, 63, 65, 66, 80, 97, 131, 150, 167, 409, 424, 425, 446, 448, 456, 486, 487, 526]

def zResidual : Multiset Lattice :=
  {(3, -2), (3, -1), (4, 17), (6, 17)}

def zCancellation : Multiset Lattice :=
  {(0, 8), (0, 9), (1, 4), (1, 5), (1, 6), (1, 8), (1, 9), (2, 4), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (3, 2), (3, 4), (3, 6), (3, 7), (4, 2), (4, 9), (4, 10), (4, 11), (5, 0), (5, 17), (6, 11), (6, 12), (6, 15), (7, 15), (8, 13)}
-- END FIXED WITNESS DATA

/-- Closed multiplication identity: 69 terms = 3 residual + twice 33. -/
theorem x_product_identity :
    syndromeTerms xImpulse xSupport = xResidual + xCancellation + xCancellation := by
  decide

/-- Closed multiplication identity: 60 terms = 4 residual + twice 28. -/
theorem z_product_identity :
    syndromeTerms zImpulse zSupport = zResidual + zCancellation + zCancellation := by
  decide

/-- Full Laurent identity at every integer exponent, including outside the board. -/
theorem x_full_syndrome (p : Lattice) :
    coefficient (syndromeTerms xImpulse xSupport) p = coefficient xResidual p := by
  rw [x_product_identity, coefficient_cancel]

theorem z_full_syndrome (p : Lattice) :
    coefficient (syndromeTerms zImpulse zSupport) p = coefficient zResidual p := by
  rw [z_product_identity, coefficient_cancel]

/-- All three residual monomials lie beyond the retained Z-check x coordinates. -/
theorem x_residual_untested (a : ZAnchor) : coefficient xResidual (zAnchor a) = 0 := by
  have ha := a.1.isLt
  simp only [coefficient, xResidual, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    zAnchor, Prod.mk.injEq]
  split_ifs <;> first | omega | norm_num

/-- All four residual monomials lie beyond the retained X-check y coordinates. -/
theorem z_residual_untested (a : XAnchor) : coefficient zResidual (xAnchor a) = 0 := by
  have ha := a.2.isLt
  simp only [coefficient, zResidual, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton,
    xAnchor, Prod.mk.injEq]
  split_ifs <;> simp_all <;> omega

def x : Vec 722 := vector xSupport
def z : Vec 722 := vector zSupport

theorem x_cycle_model : Rectangle722.code.HZ.mulVec x = 0 := by
  funext i
  change Rectangle722.code.HZ.mulVec (vector xSupport) i = 0
  rw [x_syndrome_coefficient, x_full_syndrome, x_residual_untested]

theorem z_cycle_model : Rectangle722.code.HX.mulVec z = 0 := by
  funext i
  change Rectangle722.code.HX.mulVec (vector zSupport) i = 0
  rw [z_syndrome_coefficient, z_full_syndrome, z_residual_untested]

/-- Distinct coordinate impulses are exactly the support indicator. -/
theorem vector_indicator (s : List (Fin 722)) (hs : s.Nodup) (q : Fin 722) :
    vector s q = if q ∈ s then 1 else 0 := by
  revert hs
  induction s with
  | nil => intro _; simp [vector]
  | cons a s ih =>
    intro hs
    have hs' := List.nodup_cons.mp hs
    simp only [vector, Pi.add_apply, ih hs'.2]
    by_cases h : q = a
    · subst q
      simp [Pi.single_apply, hs'.1]
    · simp [Pi.single_apply, h]

theorem vector_eq_indicator (s : List (Fin 722)) (hs : s.Nodup) :
    vector s = Sparse.indicator s.toFinset := by
  funext q
  simpa only [Sparse.indicator, List.mem_toFinset] using vector_indicator s hs q

theorem x_support_nodup : xSupport.Nodup := by decide
theorem z_support_nodup : zSupport.Nodup := by decide

theorem support_intersection : xSupport.toFinset ∩ zSupport.toFinset = {65} := by
  decide

theorem paired : x ⬝ᵥ z = 1 := by
  rw [x, z, vector_eq_indicator xSupport x_support_nodup,
    vector_eq_indicator zSupport z_support_nodup, Sparse.indicator_dot_indicator,
    support_intersection]
  simp

private theorem indicator_weight (s : Finset (Fin 722)) :
    hammingNorm (Sparse.indicator s) = s.card := by
  classical
  simp [hammingNorm, Sparse.indicator]

theorem x_weight : hammingNorm x = 23 := by
  rw [x, vector_eq_indicator xSupport x_support_nodup, indicator_weight,
    List.toFinset_card_of_nodup x_support_nodup]
  rfl

theorem z_weight : hammingNorm z = 20 := by
  rw [z, vector_eq_indicator zSupport z_support_nodup, indicator_weight,
    List.toFinset_card_of_nodup z_support_nodup]
  rfl

/-- The checked submitted matrices have these actual vector cycles. -/
theorem x_cycle : Rectangle722Submitted.code.HZ.mulVec x = 0 := by
  rw [Rectangle722Submitted.code_eq]
  exact x_cycle_model

theorem z_cycle : Rectangle722Submitted.code.HX.mulVec z = 0 := by
  rw [Rectangle722Submitted.code_eq]
  exact z_cycle_model

theorem x_logical : Rectangle722Submitted.code.IsXLogical x :=
  Rectangle722Submitted.code.x_logical_of_pair x z x_cycle z_cycle paired

theorem z_logical : Rectangle722Submitted.code.IsZLogical z :=
  Rectangle722Submitted.code.z_logical_of_pair z x z_cycle x_cycle
    ((dotProduct_comm z x).trans paired)

theorem z_upper_witness :
    ∃ v, Rectangle722Submitted.code.IsZLogical v ∧ hammingNorm v = 20 :=
  ⟨z, z_logical, z_weight⟩

/-- A concrete pure-Z nontrivial Pauli of weight 20, not merely a sector claim. -/
theorem pauli_upper_witness :
    ∃ g : NQubitPauliGroupElement Rectangle722Submitted.code.homological.numQubits,
      StabilizerGroup.IsNontrivialLogicalOperator g
        Rectangle722Submitted.code.homological.homologicalStabilizerGroup ∧
      NQubitPauliGroupElement.weight g = 20 := by
  refine ⟨Rectangle722Submitted.code.homological.chainZOperator z, ?_, ?_⟩
  · exact (HomologicalCode.chainZOperator_isNontrivialLogical_iff
      (X := Rectangle722Submitted.code.homological) z).mpr
      ((Rectangle722Submitted.code.z_logical_iff z).mp z_logical)
  · rw [HomologicalCode.weight_chainZOperator]
    exact z_weight

end QldpcVerification.Rectangle722Witness
