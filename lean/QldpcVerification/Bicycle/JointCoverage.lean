import QldpcVerification.Bicycle.SignedPaths

/-! Complete logical coverage and two-sided lattice bounds for jointly generating steps. -/

namespace QldpcVerification.Bicycle.Connected

open Matrix Module Lattice

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
theorem square_displacement (s t : ℕ) (v : ZMod m) :
    (square s t v).displacement Normalized.horizontal = 0 := by
  simp [square, hEdge, vEdge, hReverse, vReverse, Walk.single, Walk.displacement,
    Normalized.horizontal, axisX, axisY, signed]

namespace PeriodBasis

variable {s t : ℕ} (B : PeriodBasis m s t)

def periodLoop : Walk (source (m := m)) (target s t) 0 0 :=
  closedPath s t ((m : ℤ) * B.p) ((m : ℤ) * B.q) (by simp)

def transverseLoop : Walk (source (m := m)) (target s t) 0 0 :=
  closedPath s t B.b (-B.a) (by rw [B.first_step, B.second_step]; push_cast; ring)

@[simp] theorem periodLoop_displacement :
    B.periodLoop.displacement Normalized.horizontal = ((m : ℤ) * B.p, (m : ℤ) * B.q) := by
  simp [periodLoop]

@[simp] theorem transverseLoop_displacement :
    B.transverseLoop.displacement Normalized.horizontal = (B.b, -B.a) := by
  simp [transverseLoop]

theorem periodLoop_carry : B.lift.walkCarry B.periodLoop = 1 := by
  have h := B.lift.displacement_eq B.periodLoop
  rw [B.periodLoop_displacement] at h
  have hh : (m : ℤ) * B.lift.walkCarry B.periodLoop = (m : ℤ) * 1 := by
    calc
      _ = B.a * ((m : ℤ) * B.p) + B.b * ((m : ℤ) * B.q) := by
        simpa [lift] using h.symm
      _ = (m : ℤ) * (B.a * B.p + B.b * B.q) := by ring
      _ = _ := by rw [B.bezout]
  exact mul_left_cancel₀ (by exact_mod_cast (NeZero.ne m)) hh

theorem transverseLoop_carry : B.lift.walkCarry B.transverseLoop = 0 := by
  have h := B.lift.displacement_eq B.transverseLoop
  rw [B.transverseLoop_displacement] at h
  have hh : (m : ℤ) * B.lift.walkCarry B.transverseLoop = 0 := by
    change B.a * B.b + B.b * -B.a = B.potential 0 - B.potential 0 +
      (m : ℤ) * B.lift.walkCarry B.transverseLoop at h
    linear_combination -h
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast (NeZero.ne m))

def detector (i : Fin 2) (e : Edge m) : ZMod 2 :=
  if i = 0 then (B.label e).1 else (B.label e).2

def witness (i : Fin 2) : Edge m → ZMod 2 :=
  if i = 0 then B.periodLoop.binaryChain else B.transverseLoop.binaryChain

theorem witness_kernel (i : Fin 2) : (H s t).mulVec (B.witness i) = 0 := by
  unfold witness
  split
  · exact B.periodLoop.closed_chain_kernel (H s t) (fun _ _ => rfl)
  · exact B.transverseLoop.closed_chain_kernel (H s t) (fun _ _ => rfl)

theorem witness_coordinates (i : Fin 2) :
    (B.witness i ⬝ᵥ B.detector 0, B.witness i ⬝ᵥ B.detector 1) =
      if i = 0 then (1, 0) else (0, 1) := by
  fin_cases i
  · change (B.periodLoop.binaryChain ⬝ᵥ (fun e => (B.label e).1),
      B.periodLoop.binaryChain ⬝ᵥ (fun e => (B.label e).2)) = (1, 0)
    rw [← Walk.binaryChain_labels, B.label_sum, B.periodLoop_carry, B.periodLoop_displacement]
    have hz : B.q * ((m : ℤ) * B.p) - B.p * ((m : ℤ) * B.q) = 0 := by ring
    rw [hz]
    rfl
  · change (B.transverseLoop.binaryChain ⬝ᵥ (fun e => (B.label e).1),
      B.transverseLoop.binaryChain ⬝ᵥ (fun e => (B.label e).2)) = (0, 1)
    rw [← Walk.binaryChain_labels, B.label_sum, B.transverseLoop_carry,
      B.transverseLoop_displacement]
    have ho : B.q * B.b - B.p * -B.a = 1 := by linear_combination B.bezout
    rw [ho]
    rfl

theorem paired (i j : Fin 2) : B.witness i ⬝ᵥ B.detector j = if i = j then 1 else 0 := by
  have h := B.witness_coordinates i
  fin_cases i <;> fin_cases j
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem face_detector_zero (v : ZMod m) (i : Fin 2) : F s t v ⬝ᵥ B.detector i = 0 := by
  have h := B.closed_zero (square s t v) (square_displacement s t v)
  rw [Walk.binaryChain_labels] at h
  fin_cases i
  · simpa [F, detector] using congrArg Prod.fst h
  · simpa [F, detector] using congrArg Prod.snd h

end PeriodBasis

def cycles (s t : ℕ) := LinearMap.ker (H (m := m) s t).mulVecLin
def boundaries (s t : ℕ) := Submodule.span (ZMod 2) (Set.range (F (m := m) s t))

theorem boundaries_le_cycles (s t : ℕ) : boundaries (m := m) s t ≤ cycles s t := by
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  exact face_cycle s t v

theorem dimension_bound (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    finrank (ZMod 2) (cycles (m := m) s t) ≤ finrank (ZMod 2) (boundaries (m := m) s t) + 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (H (m := m) s t).mulVecLin
  have hr : finrank (ZMod 2) (LinearMap.range (H (m := m) s t).mulVecLin) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H s t))) :=
    (H s t).rank_eq_finrank_span_row
  rw [hr, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, ZMod.card] at h
  obtain ⟨hx, hz⟩ := ranks s t hc
  change _ + finrank (ZMod 2) (cycles s t) = m + m at h
  change finrank (ZMod 2) (cycles s t) ≤
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F s t))) + 2
  rw [hx] at h
  rw [hz]
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  omega

def coverageWith {s t : ℕ} (B : PeriodBasis m s t)
    (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    CoverageCertificate (cycles (m := m) s t) (boundaries s t) 2 where
  boundary_le := boundaries_le_cycles s t
  detectors := B.detector
  witnesses := B.witness
  witness_mem := B.witness_kernel
  boundary_zero := by
    have hle : boundaries (m := m) s t ≤ LinearMap.ker (pairingMap B.detector) := by
      apply Submodule.span_le.mpr
      rintro x ⟨v, rfl⟩
      ext i
      exact B.face_detector_zero v i
    intro x hx i
    exact congrFun (hle hx) i
  paired := B.paired
  dimension_bound := dimension_bound s t hc

noncomputable def coverage (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    CoverageCertificate (cycles (m := m) s t) (boundaries s t) 2 :=
  coverageWith (periodBasis hc) hc

theorem complex_cycles (s t : ℕ) : (complex (m := m) s t).cycles = cycles s t := rfl

theorem complex_boundaries (s t : ℕ) : (complex (m := m) s t).boundaries = boundaries s t := by
  change LinearMap.range (F s t).transpose.mulVecLin = _
  rw [Matrix.range_mulVecLin]
  rfl

noncomputable def complex_coverage (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    CoverageCertificate (complex (m := m) s t).cycles (complex s t).boundaries 2 := by
  rw [complex_cycles, complex_boundaries]
  exact coverage s t hc

omit [NeZero m] in
theorem step (s t : ℕ) (e : Edge m) : target s t e - source e =
    if Normalized.horizontal e then (s : ZMod m) else (t : ZMod m) := by
  cases e <;> simp [target, source, Normalized.source, Normalized.horizontal]

theorem lower (s t D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Edge m → ZMod 2) (hx : x ∈ cycles s t) (hb : x ∉ boundaries s t) :
    D ≤ hammingNorm x := by
  let B := periodBasis hc
  apply weight_ge_of_coordinate_certificate Normalized.horizontal (coverageWith B hc)
    (s : ZMod m) t source (target s t) (step s t) B.label (fun _ => B.closed_zero)
    (by intro e; simp [coverageWith, PeriodBasis.detector])
    (fun x hx => cycle_of_kernel source (target s t) (H s t) (fun _ _ => rfl) x hx)
    D hbound x hx hb

theorem pull_dual_F (s t : ℕ) (v : ZMod m) :
    pull Normalized.dualEquiv (F s t v) = H s t (-v) := by
  have h := congrArg (pull (Normalized.dualEquiv (m := m))) (pull_dual_H s t (-v))
  simpa only [Normalized.pull_dual_involutive, neg_neg] using h.symm

theorem dual_lower (s t D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (x : Edge m → ZMod 2) (hx : (F s t).mulVec x = 0)
    (hb : x ∉ Submodule.span (ZMod 2) (Set.range (H s t))) : D ≤ hammingNorm x := by
  have hcy : pull Normalized.dualEquiv x ∈ cycles s t :=
    (kernel_pull_iff Normalized.dualEquiv (F s t) (H s t) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_F s t) x).mpr hx
  have hn : pull Normalized.dualEquiv x ∉ boundaries s t := by
    intro h
    apply hb
    exact (rowspace_pull_iff Normalized.dualEquiv (H s t) (F s t) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_H s t) x).mp h
  simpa only [pull_weight] using lower s t D hc hbound (pull Normalized.dualEquiv x) hcy hn

theorem zero_displacement_boundary (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    {v : ZMod m} (w : Walk source (target s t) v v)
    (hz : w.displacement Normalized.horizontal = 0) : w.binaryChain ∈ boundaries s t := by
  let B := periodBasis hc
  apply ((coverageWith B hc).mem_boundary_iff
    (w.closed_chain_kernel (H s t) (fun _ _ => rfl))).mpr
  have h := B.closed_zero w hz
  rw [Walk.binaryChain_labels] at h
  intro i
  fin_cases i
  · simpa [coverageWith, PeriodBasis.detector] using congrArg Prod.fst h
  · simpa [coverageWith, PeriodBasis.detector] using congrArg Prod.snd h

end QldpcVerification.Bicycle.Connected
