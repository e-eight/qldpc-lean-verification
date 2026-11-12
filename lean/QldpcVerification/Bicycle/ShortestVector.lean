import QldpcVerification.Bicycle.JointMatch

/-! A shortest nonzero period relation supplies both upper distance witnesses. -/

namespace QldpcVerification.Lattice.Walk

variable {E V : Type} {source target : E → V}

@[simp] theorem length_copy {u v u' v' : V} (w : Walk source target u v)
    (hu : u = u') (hv : v = v') : (w.copy hu hv).length = w.length := by
  simp [length]

@[simp] theorem length_reverse {u v : V} (w : Walk source target u v) :
    w.reverse.length = w.length := by
  induction w with
  | nil => rfl
  | cons e r w ih =>
    simp only [reverse, length_append, length_copy, length_single]
    simpa [length, edges, Nat.add_comm] using ih

theorem binaryChain_eq_zero_of_not_mem [Fintype E] [DecidableEq E]
    {u v : V} (w : Walk source target u v) (e : E) (h : e ∉ w.edges) :
    w.binaryChain e = 0 := by
  induction w with
  | nil => rfl
  | cons f r w ih =>
    have hh : e ≠ f ∧ e ∉ w.edges := by simpa [edges] using h
    simp [binaryChain, hh.1, ih hh.2]

theorem binaryChain_weight_le_length [Fintype E] [DecidableEq E]
    {u v : V} (w : Walk source target u v) : hammingNorm w.binaryChain ≤ w.length := by
  classical
  calc
    hammingNorm w.binaryChain ≤ w.edges.toFinset.card := by
      apply Finset.card_le_card
      intro e he
      apply List.mem_toFinset.mpr
      by_contra h
      exact (Finset.mem_filter.mp he).2 (w.binaryChain_eq_zero_of_not_mem e h)
    _ ≤ w.length := List.toFinset_card_le _

end QldpcVerification.Lattice.Walk

namespace QldpcVerification.Bicycle.Connected

open Matrix Module Lattice

variable {m : ℕ} [NeZero m]

/-- The square boundary has at most four physical edges, including degenerate squares. -/
theorem face_weight_le_four (s t : ℕ) (v : ZMod m) :
    hammingNorm (F s t v) ≤ 4 := by
  have h := (square (m := m) s t v).binaryChain_weight_le_length
  simpa [F, square, hEdge, vEdge, hReverse, vReverse] using h

/-- The vertex checks satisfy the same bound through the physical dual permutation. -/
theorem vertex_weight_le_four (s t : ℕ) (v : ZMod m) :
    hammingNorm (H s t v) ≤ 4 := by
  rw [← pull_weight Normalized.dualEquiv, pull_dual_H]
  exact face_weight_le_four s t (-v)

/-- Each edge has at most two nonzero vertex incidences; loops cancel. -/
theorem vertex_column_weight_le_two (s t : ℕ) (e : Edge m) :
    hammingNorm (fun v => H s t v e) ≤ 2 := by
  classical
  have hs : Finset.univ.filter (fun v => H s t v e ≠ 0) ⊆
      {source e, target s t e} := by
    intro v hv
    by_contra hn
    have hh : source e ≠ v ∧ target s t e ≠ v := by simpa [eq_comm] using hn
    exact (Finset.mem_filter.mp hv).2 (by simp [H, incidence, hh.1, hh.2])
  calc
    hammingNorm (fun v => H s t v e) ≤ ({source e, target s t e} : Finset _).card :=
      Finset.card_le_card hs
    _ ≤ 2 := by
      rcases Finset.card_pair_eq_one_or_two (a := source e) (b := target s t e) with h | h <;>
        omega

/-- Each edge has at most two nonzero square incidences. -/
theorem face_column_weight_le_two (s t : ℕ) (e : Edge m) :
    hammingNorm (fun v => F s t v e) ≤ 2 := by
  have he (v : ZMod m) : F s t v e = H s t (-v) (Normalized.dualEquiv e) := by
    have hh := congrFun (pull_dual_H (m := m) s t (-v)) e
    simpa [pull] using hh.symm
  simp_rw [he]
  rw [show (fun v => H s t (-v) (Normalized.dualEquiv e)) =
      pull (Equiv.neg (ZMod m)) (fun v => H s t v (Normalized.dualEquiv e)) from rfl,
    pull_weight]
  exact vertex_column_weight_le_two s t (Normalized.dualEquiv e)

omit [NeZero m] in
@[simp] theorem horizontalPath_length (s t n : ℕ) (v : ZMod m) :
    (horizontalPath s t n v).length = n := by
  induction n generalizing v with
  | zero => simp [horizontalPath, Walk.length, Walk.edges]
  | succ n ih => simp [horizontalPath, hEdge, ih, Nat.add_comm]

omit [NeZero m] in
@[simp] theorem verticalPath_length (s t n : ℕ) (v : ZMod m) :
    (verticalPath s t n v).length = n := by
  induction n generalizing v with
  | zero => simp [verticalPath, Walk.length, Walk.edges]
  | succ n ih => simp [verticalPath, vEdge, ih, Nat.add_comm]

omit [NeZero m] in
@[simp] theorem horizontalIntPath_length (s t : ℕ) (u : ℤ) (v : ZMod m) :
    (horizontalIntPath s t u v).length = u.natAbs := by
  cases u <;> simp [horizontalIntPath]

omit [NeZero m] in
@[simp] theorem verticalIntPath_length (s t : ℕ) (u : ℤ) (v : ZMod m) :
    (verticalIntPath s t u v).length = u.natAbs := by
  cases u <;> simp [verticalIntPath]

@[simp] theorem closedPath_length (s t : ℕ) (u v : ℤ)
    (h : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0) :
    (closedPath s t u v h).length = u.natAbs + v.natAbs := by
  simp [closedPath, displacementPath]

/-- Vanishing winding coordinates allow an integer period displacement to be halved. -/
theorem PeriodBasis.half_relation {s t : ℕ} (B : PeriodBasis m s t) (u v : ℤ)
    (hrel : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0)
    (hz : ((closedPath s t u v hrel).edges.map B.label).sum = 0) :
    ∃ u' v' : ℤ, u = 2 * u' ∧ v = 2 * v' ∧
      (s : ZMod m) * (u' : ZMod m) + (t : ZMod m) * (v' : ZMod m) = 0 := by
  let w := closedPath s t u v hrel
  let k := B.lift.walkCarry w
  have hk : B.a * u + B.b * v = (m : ℤ) * k := by
    have hh := B.lift.displacement_eq w
    simpa [w, PeriodBasis.lift] using hh
  have hc : (k : ZMod 2) = 0 := by
    have hh := congrArg Prod.fst hz
    simpa [B.label_sum, w, k] using hh
  have hl : ((B.q * u - B.p * v : ℤ) : ZMod 2) = 0 := by
    have hh := congrArg Prod.snd hz
    simpa [B.label_sum] using hh
  obtain ⟨k', hkk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp hc
  obtain ⟨l', hll⟩ :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (B.q * u - B.p * v) 2).mp hl
  let u' := B.p * (m : ℤ) * k' + B.b * l'
  let v' := B.q * (m : ℤ) * k' - B.a * l'
  have hu : u = 2 * u' := by
    dsimp [u']
    linear_combination -u * B.bezout + B.p * hk + B.b * hll +
      B.p * (m : ℤ) * hkk
  have hv : v = 2 * v' := by
    dsimp [v']
    linear_combination -v * B.bezout + B.q * hk - B.a * hll +
      B.q * (m : ℤ) * hkk
  refine ⟨u', v', hu, hv, ?_⟩
  have hh : B.a * u' + B.b * v' = (m : ℤ) * k' := by
    dsimp [u', v']
    linear_combination (m : ℤ) * k' * B.bezout
  have hz' : (B.a : ZMod m) * (u' : ZMod m) +
      (B.b : ZMod m) * (v' : ZMod m) = 0 := by
    have hh' := congrArg (fun z : ℤ => (z : ZMod m)) hh
    simpa using hh'
  rw [B.first_step, B.second_step]
  calc
    _ = (B.scale : ZMod m) *
      ((B.a : ZMod m) * (u' : ZMod m) + (B.b : ZMod m) * (v' : ZMod m)) := by ring
    _ = 0 := by rw [hz', mul_zero]

/-- A shortest nonzero relation gives a nontrivial cycle without a stored support certificate. -/
theorem shortest_relation_cycle (s t D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hrel : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0)
    (hlen : u.natAbs + v.natAbs = D) :
    ∃ x : Edge m → ZMod 2,
      x ∈ cycles s t ∧ x ∉ boundaries s t ∧ hammingNorm x = D := by
  let B := periodBasis hc
  let w := closedPath s t u v hrel
  have hcycle : w.binaryChain ∈ cycles s t :=
    w.closed_chain_kernel (H s t) (fun _ _ => rfl)
  have hnon : w.binaryChain ∉ boundaries s t := by
    intro hb
    have hz : (w.edges.map B.label).sum = 0 := by
      rw [w.binaryChain_labels]
      apply Prod.ext
      · exact (coverageWith B hc).boundary_zero _ hb 0
      · exact (coverageWith B hc).boundary_zero _ hb 1
    obtain ⟨u', v', hu, hv, hr⟩ := B.half_relation u v hrel hz
    have hn' : u' ≠ 0 ∨ v' ≠ 0 := by
      rcases hn with hn | hn
      · exact Or.inl (by intro h; simp [h] at hu; exact hn hu)
      · exact Or.inr (by intro h; simp [h] at hv; exact hn hv)
    have hlower := hbound u' v' hn' hr
    have hpos : 0 < D := by
      rcases hn with hn | hn
      · have : 0 < u.natAbs := Int.natAbs_pos.mpr hn
        omega
      · have : 0 < v.natAbs := Int.natAbs_pos.mpr hn
        omega
    rw [hu, hv, Int.natAbs_mul, Int.natAbs_mul] at hlen
    norm_num at hlen
    omega
  refine ⟨w.binaryChain, hcycle, hnon, le_antisymm ?_ ?_⟩
  · calc
      hammingNorm w.binaryChain ≤ w.length := w.binaryChain_weight_le_length
      _ = D := by simpa [w] using hlen
  · exact lower s t D hc hbound w.binaryChain hcycle hnon

/-- Exact parameters from a hand-proved lattice minimum and one minimizing integer pair. -/
theorem Match.parameters_of_shortest {s t n mX mZ : ℕ} (M : Match m s t n mX mZ)
    (D : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 →
        D ≤ u.natAbs + v.natAbs)
    (hwitness : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 ∧
        u.natAbs + v.natAbs = D) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX D ∧ M.code.DistZ D := by
  obtain ⟨u, v, hn, hr, hl⟩ := hwitness
  obtain ⟨z, hzc, hzb, hzw⟩ := shortest_relation_cycle s t D hc hbound u v hn hr hl
  let x := pull Normalized.dualEquiv z
  have hxc : (F s t).mulVec x = 0 := by
    exact (kernel_pull_iff Normalized.dualEquiv (H s t) (F s t) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_H s t) z).mpr hzc
  have hxb : x ∉ Submodule.span (ZMod 2) (Set.range (H s t)) := by
    intro h
    exact hzb ((rowspace_pull_iff Normalized.dualEquiv (F s t) (H s t) Neg.neg
      (Equiv.neg (ZMod m)).surjective (pull_dual_F s t) z).mp h)
  apply M.parameters D hc hbound
  · refine ⟨(pull M.qubits).symm x, ?_, ?_⟩
    · apply (M.x_logical_iff _).mpr
      simpa using And.intro hxc hxb
    · have hw := pull_weight M.qubits ((pull M.qubits).symm x)
      simpa [x, pull_weight, hzw] using hw.symm
  · refine ⟨(pull M.qubits).symm z, ?_, ?_⟩
    · apply (M.z_logical_iff _).mpr
      simpa using And.intro hzc hzb
    · have hw := pull_weight M.qubits ((pull M.qubits).symm z)
      simpa [hzw] using hw.symm

/-- The period lattice has a nonzero vector: horizontal displacement equal to the period. -/
theorem relation_length_exists (s t : ℕ) :
    ∃ D : ℕ, ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 ∧
        u.natAbs + v.natAbs = D := by
  refine ⟨m, (m : ℤ), 0, Or.inl ?_, ?_, ?_⟩
  · exact_mod_cast (NeZero.ne m)
  · simp
  · simp

/-- Least nonzero physical L1 length in the integer period lattice. -/
noncomputable def minimumNorm (s t : ℕ) : ℕ := by
  classical
  exact Nat.find (relation_length_exists (m := m) s t)

theorem minimumNorm_attained (s t : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
      (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0 ∧
        u.natAbs + v.natAbs = minimumNorm (m := m) s t := by
  classical
  exact Nat.find_spec (relation_length_exists (m := m) s t)

theorem minimumNorm_lower (s t : ℕ) (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hr : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0) :
    minimumNorm (m := m) s t ≤ u.natAbs + v.natAbs := by
  classical
  exact Nat.find_min' (relation_length_exists (m := m) s t) ⟨u, v, hn, hr, rfl⟩

theorem minimumNorm_pos (s t : ℕ) : 0 < minimumNorm (m := m) s t := by
  obtain ⟨u, v, hn, _, he⟩ := minimumNorm_attained (m := m) s t
  rcases hn with hn | hn
  · have := Int.natAbs_pos.mpr hn
    omega
  · have := Int.natAbs_pos.mpr hn
    omega

/-- Unconditional exact distance for every connected cyclic binomial code. -/
theorem Match.parameters_minimum {s t n mX mZ : ℕ} (M : Match m s t n mX mZ)
    (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    (n - finrank (ZMod 2) M.code.xStab - finrank (ZMod 2) M.code.zStab = 2) ∧
      M.code.DistX (minimumNorm (m := m) s t) ∧
      M.code.DistZ (minimumNorm (m := m) s t) :=
  M.parameters_of_shortest (minimumNorm s t) hc
    (minimumNorm_lower s t) (minimumNorm_attained s t)

end QldpcVerification.Bicycle.Connected
