import QldpcVerification.Bicycle.Normalized
import QldpcVerification.Lattice.Connectivity

/-! Ranks and dimension for GB(1+x^s,1+x^t,m) when the two steps jointly generate. -/

namespace QldpcVerification.Bicycle.Connected

open Matrix Module Lattice

abbrev Edge (m : ℕ) := Normalized.Edge m
abbrev source {m : ℕ} : Edge m → ZMod m := Normalized.source

variable {m : ℕ} [NeZero m]

def target (s t : ℕ) : Edge m → ZMod m
  | .inl v => v + (s : ZMod m)
  | .inr v => v + (t : ZMod m)

def H (s t : ℕ) : Matrix (ZMod m) (Edge m) (ZMod 2) :=
  fun v e => incidence source (target s t) e v

def hEdge (s t : ℕ) (v : ZMod m) : Walk source (target s t) v (v + (s : ZMod m)) :=
  (Walk.single (.inl v) false).copy rfl rfl

def vEdge (s t : ℕ) (v : ZMod m) : Walk source (target s t) v (v + (t : ZMod m)) :=
  (Walk.single (.inr v) false).copy rfl rfl

def hReverse (s t : ℕ) (v : ZMod m) : Walk source (target s t) (v + (s : ZMod m)) v :=
  (Walk.single (.inl v) true).copy rfl rfl

def vReverse (s t : ℕ) (v : ZMod m) : Walk source (target s t) (v + (t : ZMod m)) v :=
  (Walk.single (.inr v) true).copy rfl rfl

def square (s t : ℕ) (v : ZMod m) : Walk source (target s t) v v :=
  (((hEdge s t v).append (vEdge s t (v + (s : ZMod m)))).append
    ((hReverse s t (v + (t : ZMod m))).copy (by abel) rfl)).append (vReverse s t v)

def F (s t : ℕ) : Matrix (ZMod m) (Edge m) (ZMod 2) := fun v => (square s t v).binaryChain

theorem face_cycle (s t : ℕ) (v : ZMod m) : (H s t).mulVec (F s t v) = 0 :=
  (square s t v).closed_chain_kernel (H s t) (fun _ _ => rfl)

theorem commutation (s t : ℕ) : H (m := m) s t * (F (m := m) s t).transpose = 0 := by
  ext v w
  exact congrFun (face_cycle s t w) v

theorem face_explicit (s t : ℕ) (v : ZMod m) :
    F s t v = Pi.single (.inl v) 1 + Pi.single (.inr (v + (s : ZMod m))) 1 +
      Pi.single (.inl (v + (t : ZMod m))) 1 + Pi.single (.inr v) 1 := by
  simp [F, square, hEdge, vEdge, hReverse, vReverse, Walk.single,
    Walk.binaryChain, add_assoc]

theorem pull_dual_H (s t : ℕ) (v : ZMod m) :
    pull Normalized.dualEquiv (H s t v) = F s t (-v) := by
  rw [face_explicit]
  funext e
  cases e with
  | inl w =>
    simp [pull, Normalized.dualEquiv, H, incidence, source, Normalized.source,
      target, Pi.single_apply, eq_comm, add_comm]
    have h0 : v = -w ↔ w = -v := by
      constructor <;> intro h <;> linear_combination h
    have h1 : v = (t : ZMod m) + -w ↔ w = (t : ZMod m) + -v := by
      constructor <;> intro h <;> linear_combination h
    simp only [h0, h1]
  | inr w =>
    simp [pull, Normalized.dualEquiv, H, incidence, source, Normalized.source,
      target, Pi.single_apply, eq_comm, add_comm]
    have h0 : v = -w ↔ w = -v := by
      constructor <;> intro h <;> linear_combination h
    have h1 : v = (s : ZMod m) + -w ↔ w = (s : ZMod m) + -v := by
      constructor <;> intro h <;> linear_combination h
    simp only [h0, h1]

theorem ranks (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) s t))) = m - 1 ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F (m := m) s t))) = m - 1 := by
  have hconn (f : ZMod m → ZMod 2)
      (hf : ∀ e, f (source e) = f (target s t e)) (v : ZMod m) : f v = f 0 := by
    apply constant_of_joint_periodic f s t hc
    · intro w
      simpa [source, Normalized.source, target] using (hf (.inl w)).symm
    · intro w
      simpa [source, Normalized.source, target] using (hf (.inr w)).symm
  have hr : finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) s t))) = m - 1 := by
    simpa [ZMod.card] using incidence_rank_eq source (target s t) 0 (H s t)
      (fun _ _ => rfl) hconn
  refine ⟨hr, ?_⟩
  have he := rowspace_pull (Normalized.dualEquiv (m := m)) (H s t) (F s t) Neg.neg
    (Equiv.neg (ZMod m)).surjective (pull_dual_H s t)
  rw [← he, (pull (Normalized.dualEquiv (m := m))).finrank_map_eq]
  exact hr

theorem encoded_qubits (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    (m + m) - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := m) s t))) -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F (m := m) s t))) = 2 := by
  obtain ⟨hx, hz⟩ := ranks s t hc
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [hx, hz]
  omega

def complex (s t : ℕ) : Quantum.Stabilizer.Homological.HomologicalCode where
  C0 := ZMod m
  C1 := Edge m
  C2 := ZMod m
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := (H s t).mulVecLin
  boundary2 := (F s t).transpose.mulVecLin
  boundary_comp := by
    rw [← Matrix.mulVecLin_mul, commutation s t]
    ext x v
    simp
  numQubits := m + m
  numQubits_eq := by simp [ZMod.card]
  edgeEquiv := Normalized.qubits

theorem homology_dimension (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    finrank (ZMod 2) (complex (m := m) s t).H1 = 2 := by
  rw [(complex s t).finrank_H1_eq_cycles_sub_boundaries]
  change finrank (ZMod 2) (LinearMap.ker (H s t).mulVecLin) -
    finrank (ZMod 2) (LinearMap.range (F s t).transpose.mulVecLin) = 2
  rw [Matrix.range_mulVecLin]
  change finrank (ZMod 2) (LinearMap.ker (H s t).mulVecLin) -
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F s t))) = 2
  have hn := LinearMap.finrank_range_add_finrank_ker (H (m := m) s t).mulVecLin
  have hr : finrank (ZMod 2) (LinearMap.range (H (m := m) s t).mulVecLin) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H s t))) :=
    (H s t).rank_eq_finrank_span_row
  rw [hr, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, ZMod.card] at hn
  obtain ⟨hx, hz⟩ := ranks s t hc
  rw [hx] at hn
  rw [hz]
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  omega

theorem normalized_H (t : ℕ) : H (m := m) 1 t = Normalized.H t := by
  funext v e
  cases e <;> simp [H, Normalized.H, incidence, source, Normalized.source,
    target, Normalized.target]

theorem normalized_F (t : ℕ) : F (m := m) 1 t = Normalized.F t := by
  funext v
  rw [face_explicit, Normalized.face_explicit]
  simp only [Nat.cast_one]

/-- Both generators are nonunits, but together they give both ranks five and k=2. -/
theorem nonunit_six_regression :
    Nat.gcd 2 6 ≠ 1 ∧ Nat.gcd 3 6 ≠ 1 ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := 6) 2 3))) = 5 ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F (m := 6) 2 3))) = 5 ∧
    (6 + 6) - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (H (m := 6) 2 3))) -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (F (m := 6) 2 3))) = 2 :=
  ⟨by decide, by decide, (ranks (m := 6) 2 3 (by decide)).1,
    (ranks (m := 6) 2 3 (by decide)).2, encoded_qubits (m := 6) 2 3 (by decide)⟩

/-- A shared factor leaves a nonconstant function invariant along every edge. -/
theorem disconnected_six_regression :
    ∃ f : ZMod 6 → ZMod 2,
      (∀ e, f (source e) = f (target 2 4 e)) ∧ f 1 ≠ f 0 := by
  refine ⟨fun v => (v.val : ZMod 2), ?_, ?_⟩ <;> decide +kernel

end QldpcVerification.Bicycle.Connected
