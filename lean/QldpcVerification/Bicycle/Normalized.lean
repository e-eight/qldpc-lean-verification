import QldpcVerification.Bicycle.Walks
import QldpcVerification.Lattice.IncidenceRank
import QldpcVerification.Transport

/-! The normalized binary bicycle family GB(1+x,1+x^a,m).
Coverage is constructed symbolically from closed walks, including even m and a.
Edges retain their block and source labels, so loops and parallel edges are allowed.
-/

namespace QldpcVerification.Bicycle.Normalized

open Matrix Module Lattice

abbrev Edge (m : ℕ) := ZMod m ⊕ ZMod m

variable {m : ℕ} [NeZero m]

def source : Edge m → ZMod m := Sum.elim id id

def horizontal : Edge m → Bool
  | .inl _ => true
  | .inr _ => false

def target (a : ℕ) : Edge m → ZMod m
  | .inl v => v + 1
  | .inr v => v + (a : ZMod m)

def H (a : ℕ) : Matrix (ZMod m) (Edge m) (ZMod 2) :=
  fun v e => incidence source (target a) e v

def hEdge (a : ℕ) (v : ZMod m) : Walk source (target a) v (v + 1) :=
  (Walk.single (.inl v) false).copy rfl rfl

def vEdge (a : ℕ) (v : ZMod m) : Walk source (target a) v (v + (a : ZMod m)) :=
  (Walk.single (.inr v) false).copy rfl rfl

def hReverse (a : ℕ) (v : ZMod m) : Walk source (target a) (v + 1) v :=
  (Walk.single (.inl v) true).copy rfl rfl

def vReverse (a : ℕ) (v : ZMod m) : Walk source (target a) (v + (a : ZMod m)) v :=
  (Walk.single (.inr v) true).copy rfl rfl

def horizontalPath (a : ℕ) : (n : ℕ) → Walk (source (m := m)) (target a) 0 (n : ZMod m)
  | 0 => (Walk.nil 0).copy rfl (by simp)
  | n + 1 => (horizontalPath a n).append ((hEdge a (n : ZMod m)).copy rfl (by simp))

def horizontalLoop (a : ℕ) : Walk (source (m := m)) (target a) 0 0 :=
  (horizontalPath a m).copy rfl (by simp)

def crossLoop (a : ℕ) : Walk (source (m := m)) (target a) 0 0 :=
  (horizontalPath a a).append ((vReverse a 0).copy (by simp) rfl)

def square (a : ℕ) (v : ZMod m) : Walk source (target a) v v :=
  (((hEdge a v).append (vEdge a (v + 1))).append
    ((hReverse a (v + (a : ZMod m))).copy (by abel) rfl)).append (vReverse a v)

def F (a : ℕ) : Matrix (ZMod m) (Edge m) (ZMod 2) :=
  fun v => (square a v).binaryChain

omit [NeZero m] in
theorem hEdge_displacement (a : ℕ) (v : ZMod m) :
    (hEdge a v).displacement horizontal = (1, 0) := by
  simp [hEdge, Walk.single, Walk.displacement, axisX, axisY, horizontal, signed]

omit [NeZero m] in
theorem vEdge_displacement (a : ℕ) (v : ZMod m) :
    (vEdge a v).displacement horizontal = (0, 1) := by
  simp [vEdge, Walk.single, Walk.displacement, axisX, axisY, horizontal, signed]

omit [NeZero m] in
theorem hReverse_displacement (a : ℕ) (v : ZMod m) :
    (hReverse a v).displacement horizontal = (-1, 0) := by
  simp [hReverse, Walk.single, Walk.displacement, axisX, axisY, horizontal, signed]

omit [NeZero m] in
theorem vReverse_displacement (a : ℕ) (v : ZMod m) :
    (vReverse a v).displacement horizontal = (0, -1) := by
  simp [vReverse, Walk.single, Walk.displacement, axisX, axisY, horizontal, signed]

omit [NeZero m] in
theorem horizontalPath_displacement (a n : ℕ) :
    (horizontalPath (m := m) a n).displacement horizontal = ((n : ℤ), 0) := by
  induction n with
  | zero => simp [horizontalPath, Walk.displacement]
  | succ n ih => simp [horizontalPath, ih, hEdge_displacement, Nat.cast_add, Nat.cast_one]

omit [NeZero m] in
theorem horizontalLoop_displacement (a : ℕ) :
    (horizontalLoop (m := m) a).displacement horizontal = ((m : ℤ), 0) := by
  simp [horizontalLoop, horizontalPath_displacement]

omit [NeZero m] in
theorem crossLoop_displacement (a : ℕ) :
    (crossLoop (m := m) a).displacement horizontal = ((a : ℤ), -1) := by
  simp [crossLoop, horizontalPath_displacement, vReverse_displacement]

omit [NeZero m] in
theorem square_displacement (a : ℕ) (v : ZMod m) :
    (square a v).displacement horizontal = 0 := by
  simp [square, hEdge_displacement, vEdge_displacement,
    hReverse_displacement, vReverse_displacement]

theorem face_cycle (a : ℕ) (v : ZMod m) : (H a).mulVec (F a v) = 0 :=
  (square a v).closed_chain_kernel (H a) (fun _ _ => rfl)

theorem commutation (a : ℕ) : H (m := m) a * (F (m := m) a).transpose = 0 := by
  ext v w
  exact congrFun (face_cycle a w) v

theorem face_explicit (a : ℕ) (v : ZMod m) :
    F a v = Pi.single (.inl v) 1 + Pi.single (.inr (v + 1)) 1 +
      Pi.single (.inl (v + (a : ZMod m))) 1 + Pi.single (.inr v) 1 := by
  simp [F, square, hEdge, vEdge, hReverse, vReverse, Walk.single,
    Walk.binaryChain, add_assoc]

omit [NeZero m] in
theorem H_explicit (a : ℕ) (v : ZMod m) :
    H a v = Pi.single (.inl v) 1 + Pi.single (.inl (v - 1)) 1 +
      Pi.single (.inr v) 1 + Pi.single (.inr (v - (a : ZMod m))) 1 := by
  funext e
  cases e <;> simp [H, incidence, source, target, Pi.single_apply,
    eq_sub_iff_add_eq, eq_comm]

omit [NeZero m] in
theorem step (a : ℕ) (e : Edge m) : target a e - source e =
    if horizontal e then (1 : ZMod m) else (a : ZMod m) := by
  cases e <;> simp [target, source, horizontal]

def lift (a : ℕ) : WindingData (source (m := m)) (target a) horizontal :=
  cyclicWindingData source (target a) horizontal 1 a (by simpa using step a)

def detector (a : ℕ) (i : Fin 2) (e : Edge m) : ZMod 2 :=
  if i = 0 then ((lift a).label e).1 else ((lift a).label e).2

def witness (a : ℕ) (i : Fin 2) : Edge m → ZMod 2 :=
  if i = 0 then (horizontalLoop a).binaryChain else (crossLoop a).binaryChain

theorem witness_kernel (a : ℕ) (i : Fin 2) : (H a).mulVec (witness (m := m) a i) = 0 := by
  unfold witness
  split
  · exact (horizontalLoop a).closed_chain_kernel (H a) (fun _ _ => rfl)
  · exact (crossLoop a).closed_chain_kernel (H a) (fun _ _ => rfl)

theorem face_labels (a : ℕ) (v : ZMod m) :
    ((square a v).edges.map (lift a).label).sum = 0 :=
  (lift a).closed_zero _ (square_displacement a v)

theorem horizontalLoop_carry (a : ℕ) :
    (lift a).walkCarry (horizontalLoop (m := m) a) = 1 := by
  have h := (lift a).displacement_eq (horizontalLoop (m := m) a)
  rw [horizontalLoop_displacement] at h
  have hh : (m : ℤ) * (lift (m := m) a).walkCarry (horizontalLoop a) = (m : ℤ) * 1 := by
    simpa [lift, cyclicWindingData] using h.symm
  exact mul_left_cancel₀ (by exact_mod_cast (NeZero.ne m)) hh

theorem crossLoop_carry (a : ℕ) :
    (lift a).walkCarry (crossLoop (m := m) a) = 0 := by
  have h := (lift a).displacement_eq (crossLoop (m := m) a)
  rw [crossLoop_displacement] at h
  have hh : (m : ℤ) * (lift (m := m) a).walkCarry (crossLoop a) = 0 := by
    simpa [lift, cyclicWindingData] using h.symm
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast (NeZero.ne m))

theorem witness_coordinates (a : ℕ) (i : Fin 2) :
    (witness (m := m) a i ⬝ᵥ detector a 0, witness (m := m) a i ⬝ᵥ detector a 1) =
      if i = 0 then (1, 0) else (0, 1) := by
  fin_cases i
  · change ((horizontalLoop a).binaryChain ⬝ᵥ (fun e => ((lift a).label e).1),
      (horizontalLoop a).binaryChain ⬝ᵥ (fun e => ((lift a).label e).2)) = (1, 0)
    rw [← Walk.binaryChain_labels, (lift a).label_sum, horizontalLoop_carry,
      horizontalLoop_displacement]
    rfl
  · change ((crossLoop a).binaryChain ⬝ᵥ (fun e => ((lift a).label e).1),
      (crossLoop a).binaryChain ⬝ᵥ (fun e => ((lift a).label e).2)) = (0, 1)
    rw [← Walk.binaryChain_labels, (lift a).label_sum, crossLoop_carry,
      crossLoop_displacement]
    apply Prod.ext
    · rfl
    · change (-1 : ZMod 2) = 1
      decide

theorem paired (a : ℕ) (i j : Fin 2) :
    witness (m := m) a i ⬝ᵥ detector a j = if i = j then 1 else 0 := by
  have h := witness_coordinates (m := m) a i
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem face_detector_zero (a : ℕ) (v : ZMod m) (j : Fin 2) :
    F a v ⬝ᵥ detector a j = 0 := by
  have h := face_labels a v
  rw [Walk.binaryChain_labels] at h
  fin_cases j
  · simpa [F, detector] using congrArg Prod.fst h
  · simpa [F, detector] using congrArg Prod.snd h

def dualEquiv : Edge m ≃ Edge m where
  toFun | .inl v => .inr (-v) | .inr v => .inl (-v)
  invFun | .inl v => .inr (-v) | .inr v => .inl (-v)
  left_inv e := by cases e <;> simp
  right_inv e := by cases e <;> simp

theorem pull_dual_H (a : ℕ) (v : ZMod m) :
    pull dualEquiv (H a v) = F a (-v) := by
  rw [face_explicit]
  funext e
  cases e with
  | inl w =>
    simp [pull, dualEquiv, H, incidence, source, target, Pi.single_apply, eq_comm, add_comm]
    have h0 : v = -w ↔ w = -v := by
      constructor <;> intro h <;> linear_combination h
    have h1 : v = (a : ZMod m) + -w ↔ w = (a : ZMod m) + -v := by
      constructor <;> intro h <;> linear_combination h
    simp only [h0, h1]
  | inr w =>
    simp [pull, dualEquiv, H, incidence, source, target, Pi.single_apply, eq_comm, add_comm]
    have h0 : v = -w ↔ w = -v := by
      constructor <;> intro h <;> linear_combination h
    have h1 : v = -w + 1 ↔ w = -v + 1 := by
      constructor <;> intro h <;> linear_combination h
    simp only [h0, h1]

omit [NeZero m] in
theorem pull_dual_involutive (x : Edge m → ZMod 2) :
    pull dualEquiv (pull dualEquiv x) = x := by
  funext e
  cases e <;> simp [pull, dualEquiv]

theorem pull_dual_F (a : ℕ) (v : ZMod m) :
    pull dualEquiv (F a v) = H a (-v) := by
  have h := congrArg (pull (dualEquiv (m := m))) (pull_dual_H a (-v))
  simpa only [pull_dual_involutive, neg_neg] using h.symm

def cycles (a : ℕ) := LinearMap.ker (H (m := m) a).mulVecLin
def boundaries (a : ℕ) := Submodule.span (ZMod 2) (Set.range (F (m := m) a))

theorem boundaries_le_cycles (a : ℕ) : boundaries (m := m) a ≤ cycles a := by
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  exact face_cycle a v

theorem rank_H_lower (a : ℕ) :
    m - 1 ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) := by
  have hc (f : ZMod m → ZMod 2)
      (hf : ∀ e, f (source e) = f (target a e)) : ∀ v, f v = f 0 := by
    intro v
    apply constant_of_periodic f 1 1 (by simp) (fun w => ?_) v
    simpa [source, target] using (hf (.inl w)).symm
  simpa [ZMod.card] using incidence_rank_lower source (target a) 0 (H a)
    (fun _ _ => rfl) hc

theorem rank_F_eq_H (a : ℕ) :
    finrank (ZMod 2) (boundaries (m := m) a) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) := by
  have h := rowspace_pull (dualEquiv (m := m)) (H a) (F a) Neg.neg
    (Equiv.neg (ZMod m)).surjective (pull_dual_H a)
  rw [boundaries, ← h]
  exact (pull (dualEquiv (m := m))).finrank_map_eq _

theorem dimension_bound (a : ℕ) :
    finrank (ZMod 2) (cycles (m := m) a) ≤ finrank (ZMod 2) (boundaries (m := m) a) + 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (H (m := m) a).mulVecLin
  have hr : finrank (ZMod 2) (LinearMap.range (H (m := m) a).mulVecLin) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) :=
    (H (m := m) a).rank_eq_finrank_span_row
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, ZMod.card] at h
  rw [hr] at h
  rw [rank_F_eq_H]
  have hl := rank_H_lower (m := m) a
  change _ + finrank (ZMod 2) (cycles a) = m + m at h
  omega

def coverage (a : ℕ) : CoverageCertificate (cycles (m := m) a) (boundaries a) 2 where
  boundary_le := boundaries_le_cycles a
  detectors := detector a
  witnesses := witness a
  witness_mem := witness_kernel a
  boundary_zero := by
    have hle : boundaries (m := m) a ≤ LinearMap.ker (pairingMap (detector a)) := by
      apply Submodule.span_le.mpr
      rintro x ⟨v, rfl⟩
      ext j
      exact face_detector_zero a v j
    intro x hx j
    exact congrFun (hle hx) j
  paired := paired a
  dimension_bound := dimension_bound a

theorem rank_nullity (a : ℕ) :
    finrank (ZMod 2) (cycles (m := m) a) +
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) = m + m := by
  have h := LinearMap.finrank_range_add_finrank_ker (H (m := m) a).mulVecLin
  have hr : finrank (ZMod 2) (LinearMap.range (H (m := m) a).mulVecLin) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) :=
    (H (m := m) a).rank_eq_finrank_span_row
  rw [hr, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, ZMod.card] at h
  exact (add_comm _ _).trans h

theorem ranks (a : ℕ) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) = m - 1 ∧
      finrank (ZMod 2) (boundaries (m := m) a) = m - 1 := by
  have hc := (coverage (m := m) a).dimension_eq
  have hr := rank_nullity (m := m) a
  have he := rank_F_eq_H (m := m) a
  omega

theorem encoded_qubits (a : ℕ) :
    (m + m) - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) a))) -
      finrank (ZMod 2) (boundaries (m := m) a) = 2 := by
  have hc := (coverage (m := m) a).dimension_eq
  have hr := rank_nullity (m := m) a
  omega

def qubits : Edge m ≃ Fin (m + m) :=
  (Equiv.sumCongr (ZMod.finEquiv m).symm.toEquiv
    (ZMod.finEquiv m).symm.toEquiv).trans finSumFinEquiv

def complex (a : ℕ) : Quantum.Stabilizer.Homological.HomologicalCode where
  C0 := ZMod m
  C1 := Edge m
  C2 := ZMod m
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := (H a).mulVecLin
  boundary2 := (F a).transpose.mulVecLin
  boundary_comp := by
    rw [← Matrix.mulVecLin_mul, commutation a]
    ext x v
    simp
  numQubits := m + m
  numQubits_eq := by simp [ZMod.card]
  edgeEquiv := qubits

theorem complex_cycles (a : ℕ) : (complex (m := m) a).cycles = cycles a := rfl

theorem complex_boundaries (a : ℕ) : (complex (m := m) a).boundaries = boundaries a := by
  change LinearMap.range (F a).transpose.mulVecLin = _
  rw [Matrix.range_mulVecLin]
  rfl

def complex_coverage (a : ℕ) :
    CoverageCertificate (complex (m := m) a).cycles (complex (m := m) a).boundaries 2 := by
  rw [complex_cycles, complex_boundaries]
  exact coverage a

theorem lower (a D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Edge m → ZMod 2) (hx : x ∈ cycles a) (hb : x ∉ boundaries a) :
    D ≤ hammingNorm x := by
  apply weight_ge_of_coordinate_certificate horizontal (coverage a) (1 : ZMod m) a
    source (target a) (step a) (lift a).label (fun _ => (lift a).closed_zero)
    (by intro e; simp [coverage, detector])
    (fun x hx => cycle_of_kernel source (target a) (H a) (fun _ _ => rfl) x hx)
    D hbound x hx hb

theorem dual_lower (a D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (1 : ZMod m) * (u : ZMod m) + (a : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Edge m → ZMod 2) (hx : (F a).mulVec x = 0)
    (hb : x ∉ Submodule.span (ZMod 2) (Set.range (H a))) : D ≤ hammingNorm x := by
  have hc : pull dualEquiv x ∈ cycles a :=
    (kernel_pull_iff dualEquiv (F a) (H a) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_F a) x).mpr hx
  have hn : pull dualEquiv x ∉ boundaries a := by
    intro h
    apply hb
    exact (rowspace_pull_iff dualEquiv (H a) (F a) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_H a) x).mp h
  simpa only [pull_weight] using lower a D hbound (pull dualEquiv x) hc hn

end QldpcVerification.Bicycle.Normalized
