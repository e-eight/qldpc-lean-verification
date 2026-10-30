import QldpcVerification.Lattice.Displacement
import QldpcVerification.Coverage

/-! Period-aware logical coordinates for the lattice bound of Arnault, Gaborit,
and Saussay, arXiv:2507.21237, Theorem II.7 and Corollary II.8.

The displacement argument accepts any edge labels that vanish on closed walks
of zero integer displacement. Integer lifts certify this property for winding
coordinates, including when the number of vertices is even. Complete logical
detection remains a separate, checked linear-algebra obligation.
-/

namespace QldpcVerification.Lattice

variable {E V : Type} (source target : E → V) (horizontal : E → Bool)

/-- An integer potential and period carry for each oriented edge. -/
structure WindingData where
  a : ℤ
  b : ℤ
  period : ℤ
  period_ne_zero : period ≠ 0
  potential : V → ℤ
  carry : E → ℤ
  edge_eq : ∀ e, a * axisX horizontal e + b * axisY horizontal e =
    potential (target e) - potential (source e) + period * carry e

/-- The standard integer lift of any two-step cyclic graph. Carries count
crossings of the chosen fundamental interval, with signs retained over ℤ. -/
def cyclicWindingData {m : ℕ} [NeZero m] (source target : E → ZMod m)
    (horizontal : E → Bool) (a b : ℤ)
    (hstep : ∀ e, target e - source e =
      if horizontal e then (a : ZMod m) else (b : ZMod m)) :
    WindingData source target horizontal where
  a := a
  b := b
  period := m
  period_ne_zero := by exact_mod_cast (NeZero.ne m)
  potential v := v.val
  carry e := (a * axisX horizontal e + b * axisY horizontal e -
    ((target e).val - (source e).val : ℤ)) / m
  edge_eq e := by
    have hs : target e - source e =
        (a : ZMod m) * (axisX horizontal e : ZMod m) +
          (b : ZMod m) * (axisY horizontal e : ZMod m) := by
      cases h : horizontal e <;> simpa [axisX, axisY, h] using hstep e
    have hd : (m : ℤ) ∣ a * axisX horizontal e + b * axisY horizontal e -
        ((target e).val - (source e).val : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_zmod_val] using (sub_eq_zero.mpr hs.symm)
    rw [mul_comm (m : ℤ), Int.ediv_mul_cancel hd]
    ring

namespace WindingData

variable {source target horizontal} (L : WindingData source target horizontal)

def label (e : E) : ZMod 2 × ZMod 2 :=
  ((L.carry e : ZMod 2), (axisY horizontal e : ZMod 2))

def walkCarry : {u v : V} → Walk source target u v → ℤ
  | _, _, .nil _ => 0
  | _, _, .cons e r p => signed r (L.carry e) + walkCarry p

theorem signed_edge (e : E) (r : Bool) :
    L.a * signed r (axisX horizontal e) + L.b * signed r (axisY horizontal e) =
      L.potential (stepTarget source target e r) -
        L.potential (stepSource source target e r) + L.period * signed r (L.carry e) := by
  have h := L.edge_eq e
  cases r <;> simp only [signed, stepSource, stepTarget, Bool.false_eq_true, if_false, if_true]
  · exact h
  · linear_combination -h

theorem displacement_eq {u v : V} (p : Walk source target u v) :
    L.a * (p.displacement horizontal).1 + L.b * (p.displacement horizontal).2 =
      L.potential v - L.potential u + L.period * L.walkCarry p := by
  induction p with
  | nil => simp [Walk.displacement, walkCarry]
  | cons e r p ih =>
    have hs := L.signed_edge e r
    simp only [Walk.displacement, walkCarry]
    linear_combination hs + ih

theorem label_sum {u v : V} (p : Walk source target u v) :
    (p.edges.map L.label).sum =
      ((L.walkCarry p : ZMod 2), ((p.displacement horizontal).2 : ZMod 2)) := by
  induction p with
  | nil => rfl
  | cons e r p ih =>
    have hn : ∀ z : ZMod 2, -z = z := by decide
    cases r <;> simp [Walk.edges, List.map_cons, List.sum_cons, ih,
      label, walkCarry, Walk.displacement, signed, hn]

theorem closed_zero {v : V} (p : Walk source target v v)
    (hz : p.displacement horizontal = 0) : (p.edges.map L.label).sum = 0 := by
  have h := L.displacement_eq p
  rw [hz] at h
  have hc : L.walkCarry p = 0 := by
    have hp : L.period * L.walkCarry p = 0 := by simpa using h.symm
    exact (mul_eq_zero.mp hp).resolve_left L.period_ne_zero
  rw [L.label_sum, hz, hc]
  rfl

end WindingData

theorem cycle_potential_sum [Fintype V] [DecidableEq V]
    (S : Finset E) (hc : IsCycle source target S) (f : V → ZMod 2) :
    ∑ e ∈ S, (f (target e) - f (source e)) = 0 := by
  classical
  have hh : (∑ e ∈ S, ∑ v, incidence source target e v * f v) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro v _
    rw [← Finset.sum_mul, hc v, zero_mul]
  simp only [incidence, add_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_add_distrib] at hh
  simp at hh
  have hn : ∀ z : ZMod 2, -z = z := by decide
  simpa only [sub_eq_add_neg, hn, add_comm, Finset.sum_add_distrib] using hh

namespace WindingData

variable {source target horizontal} [Fintype V] [DecidableEq V]
    (L : WindingData source target horizontal)

/-- For odd period and odd first step, the old raw parities are recovered from
the winding coordinates on cycles. This permits a checked migration of the
earlier odd-length instance without changing its logical-coverage certificate. -/
theorem detects_of_axis (hperiod : (L.period : ZMod 2) = 1) (ha : (L.a : ZMod 2) = 1)
    (S : Finset E) (hc : IsCycle source target S)
    (hl : ∑ e ∈ S, axisLabel horizontal e ≠ 0) : ∑ e ∈ S, L.label e ≠ 0 := by
  intro hz
  have hcarry : (∑ e ∈ S, (L.carry e : ZMod 2)) = 0 := by
    simpa only [Prod.fst_sum, Prod.fst_zero, label] using congrArg Prod.fst hz
  have hy : (∑ e ∈ S, (axisY horizontal e : ZMod 2)) = 0 := by
    simpa only [Prod.snd_sum, Prod.snd_zero, label] using congrArg Prod.snd hz
  have he (e : E) :
      (axisX horizontal e : ZMod 2) + (L.b : ZMod 2) * (axisY horizontal e : ZMod 2) =
        ((L.potential (target e) : ZMod 2) - (L.potential (source e) : ZMod 2)) +
          (L.carry e : ZMod 2) := by
    have h := congrArg (fun z : ℤ => (z : ZMod 2)) (L.edge_eq e)
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_sub, hperiod, ha, one_mul] using h
  have hs := Finset.sum_congr rfl (fun e (_ : e ∈ S) => he e)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [cycle_potential_sum source target S hc (fun v => (L.potential v : ZMod 2)),
    hcarry, hy, mul_zero, add_zero, zero_add] at hs
  apply hl
  apply Prod.ext
  · simpa only [Prod.fst_sum, Prod.fst_zero, axisLabel] using hs
  · simpa only [Prod.snd_sum, Prod.snd_zero, axisLabel] using hy

end WindingData

/-- A detected closed trail has a nonzero lift whenever its labels vanish on
zero-displacement closed walks. No raw axis-parity assumption is needed. -/
theorem exists_short_relation_of_labels [DecidableEq E] {m : ℕ}
    (source target : E → ZMod m) (a b : ZMod m)
    (hstep : ∀ e, target e - source e = if horizontal e then a else b)
    {A : Type} [AddCommGroup A] (label : E → A)
    (hzero : ∀ v (p : Walk source target v v), p.displacement horizontal = 0 →
      (p.edges.map label).sum = 0)
    (S : Finset E) (hc : IsCycle source target S) (hl : ∑ e ∈ S, label e ≠ 0) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ a * (u : ZMod m) + b * (v : ZMod m) = 0 ∧
      u.natAbs + v.natAbs ≤ S.card := by
  classical
  obtain ⟨w, p, hn, hs, hp⟩ := detected_closed_trail source target label S hc hl
  refine ⟨(p.displacement horizontal).1, (p.displacement horizontal).2, ?_, ?_, ?_⟩
  · by_contra h
    simp only [not_or, not_not] at h
    exact hp (hzero w p (Prod.ext h.1 h.2))
  · simpa using p.displacement_relation horizontal a b source target hstep
  · exact (p.displacement_norm_le horizontal).trans (p.length_le_card S hn hs)

section BinarySupport

open Matrix

variable [Fintype E] [DecidableEq E]

namespace Walk

variable {source target}

/-- The binary chain of a walk. An edge traversed twice cancels. -/
def binaryChain : {u v : V} → Walk source target u v → (E → ZMod 2)
  | _, _, .nil _ => 0
  | _, _, .cons e _ p => Pi.single e 1 + binaryChain p

theorem binaryChain_dot {u v : V} (p : Walk source target u v) (f : E → ZMod 2) :
    p.binaryChain ⬝ᵥ f = (p.edges.map f).sum := by
  induction p with
  | nil => simp [binaryChain, edges]
  | cons e r p ih => simp [binaryChain, edges, add_dotProduct, ih]

theorem binaryChain_labels {u v : V} (p : Walk source target u v)
    (label : E → ZMod 2 × ZMod 2) :
    (p.edges.map label).sum =
      (p.binaryChain ⬝ᵥ (fun e => (label e).1),
       p.binaryChain ⬝ᵥ (fun e => (label e).2)) := by
  induction p with
  | nil => simp only [binaryChain, edges, List.map_nil, List.sum_nil, zero_dotProduct]; rfl
  | cons e r p ih =>
    simp only [edges, List.map_cons, List.sum_cons, ih, binaryChain,
      add_dotProduct, single_dotProduct, one_mul]
    rfl

theorem closed_chain_kernel [Fintype V] [DecidableEq V]
    (H : Matrix V E (ZMod 2)) (hH : ∀ v e, H v e = incidence source target e v)
    {v : V} (p : Walk source target v v) : H.mulVec p.binaryChain = 0 := by
  funext w
  change H w ⬝ᵥ p.binaryChain = 0
  rw [dotProduct_comm, binaryChain_dot]
  rw [show H w = fun e => incidence source target e w from funext (hH w)]
  rw [p.incidence_sum]
  by_cases h : v = w <;> simp [h, ← two_mul, two_eq_zero]

end Walk

/-- The AGS zero-lift-to-boundary implication, discharged algebraically from
complete winding coordinates. The cycle-space membership is explicit. -/
theorem zero_displacement_boundary
    {S B : Submodule (ZMod 2) (E → ZMod 2)}
    (C : QldpcVerification.CoverageCertificate S B 2)
    (L : WindingData source target horizontal)
    (hlabels : ∀ e, (C.detectors 0 e, C.detectors 1 e) = L.label e)
    {v : V} (p : Walk source target v v) (hp : p.binaryChain ∈ S)
    (hz : p.displacement horizontal = 0) : p.binaryChain ∈ B := by
  apply (C.mem_boundary_iff hp).mpr
  have h := L.closed_zero p hz
  rw [p.binaryChain_labels] at h
  have h0 : (fun e => (L.label e).1) = C.detectors 0 :=
    funext fun e => (congrArg Prod.fst (hlabels e)).symm
  have h1 : (fun e => (L.label e).2) = C.detectors 1 :=
    funext fun e => (congrArg Prod.snd (hlabels e)).symm
  rw [h0, h1] at h
  intro j
  fin_cases j
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

omit [DecidableEq E] in
theorem label_sum_ne_zero_of_coordinates (label : E → ZMod 2 × ZMod 2)
    (x : E → ZMod 2) (detectors : Fin 2 → E → ZMod 2)
    (h0 : ∀ e, detectors 0 e = (label e).1)
    (h1 : ∀ e, detectors 1 e = (label e).2)
    (hp : ∃ j, x ⬝ᵥ detectors j = 1) : ∑ e ∈ binarySupport x, label e ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hp
  have hf := congrArg Prod.fst hz
  have hs := congrArg Prod.snd hz
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at hf hs
  simp_rw [← h0] at hf
  simp_rw [← h1] at hs
  rw [sum_support_eq_dot] at hf hs
  fin_cases j <;> simp_all

theorem weight_ge_of_labels {m : ℕ} (a b : ZMod m)
    (source target : E → ZMod m)
    (hstep : ∀ e, target e - source e = if horizontal e then a else b)
    {A : Type} [AddCommGroup A] (label : E → A)
    (hzero : ∀ v (p : Walk source target v v), p.displacement horizontal = 0 →
      (p.edges.map label).sum = 0)
    (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      a * (u : ZMod m) + b * (v : ZMod m) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : E → ZMod 2) (hc : IsCycle source target (binarySupport x))
    (hl : ∑ e ∈ binarySupport x, label e ≠ 0) : D ≤ hammingNorm x := by
  obtain ⟨u, v, hn, he, hw⟩ := exists_short_relation_of_labels horizontal source target
    a b hstep label hzero _ hc hl
  exact (hbound u v hn he).trans hw

/-- A lattice bound for all logical classes, with complete detection supplied
by QECLean's cycle and boundary spaces through a coverage certificate. -/
theorem weight_ge_of_coordinate_certificate {m : ℕ}
    {S B : Submodule (ZMod 2) (E → ZMod 2)}
    (C : QldpcVerification.CoverageCertificate S B 2)
    (a b : ZMod m) (source target : E → ZMod m)
    (hstep : ∀ e, target e - source e = if horizontal e then a else b)
    (label : E → ZMod 2 × ZMod 2)
    (hzero : ∀ v (p : Walk source target v v), p.displacement horizontal = 0 →
      (p.edges.map label).sum = 0)
    (hlabels : ∀ e, (C.detectors 0 e, C.detectors 1 e) = label e)
    (hcycles : ∀ x, x ∈ S → IsCycle source target (binarySupport x))
    (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      a * (u : ZMod m) + b * (v : ZMod m) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : E → ZMod 2) (hx : x ∈ S) (hb : x ∉ B) : D ≤ hammingNorm x := by
  apply weight_ge_of_labels horizontal a b source target hstep label hzero D hbound x (hcycles x hx)
  exact label_sum_ne_zero_of_coordinates label x C.detectors
    (fun e => congrArg Prod.fst (hlabels e))
    (fun e => congrArg Prod.snd (hlabels e)) (C.detects hx hb)

end BinarySupport
end QldpcVerification.Lattice
