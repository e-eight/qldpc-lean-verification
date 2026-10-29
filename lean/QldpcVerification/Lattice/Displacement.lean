import QldpcVerification.Lattice.Trail
import Mathlib.InformationTheory.Hamming

/-! A binary cycle with nonzero direction parity yields a short lattice relation. -/

namespace QldpcVerification.Lattice

variable {E V : Type} (source target : E → V) (horizontal : E → Bool)

def axisX (e : E) : ℤ := if horizontal e then 1 else 0
def axisY (e : E) : ℤ := if horizontal e then 0 else 1
def signed (r : Bool) (a : ℤ) : ℤ := if r then -a else a
def axisLabel (e : E) : ZMod 2 × ZMod 2 :=
  ((axisX horizontal e : ℤ), (axisY horizontal e : ℤ))

namespace Walk

variable {source target}

def displacement : {u v : V} → Walk source target u v → ℤ × ℤ
  | _, _, .nil _ => (0, 0)
  | _, _, .cons e r p =>
      (signed r (axisX horizontal e) + (displacement p).1,
       signed r (axisY horizontal e) + (displacement p).2)

theorem label_sum {u v : V} (p : Walk source target u v) :
    (p.edges.map (axisLabel horizontal)).sum =
      (((p.displacement horizontal).1 : ZMod 2), ((p.displacement horizontal).2 : ZMod 2)) := by
  induction p with
  | nil => rfl
  | cons e r p ih =>
    simp only [edges, List.map_cons, List.sum_cons, ih, displacement]
    have hn : (-1 : ZMod 2) = 1 := by decide
    cases h : horizontal e <;> cases r <;>
      simp [axisLabel, axisX, axisY, signed, h, hn]

theorem displacement_norm_le {u v : V} (p : Walk source target u v) :
    (p.displacement horizontal).1.natAbs + (p.displacement horizontal).2.natAbs ≤ p.length := by
  induction p with
  | nil => simp [displacement, length, edges]
  | cons e r p ih =>
    have hx := Int.natAbs_add_le (signed r (axisX horizontal e)) (p.displacement horizontal).1
    have hy := Int.natAbs_add_le (signed r (axisY horizontal e)) (p.displacement horizontal).2
    have hs : (signed r (axisX horizontal e)).natAbs +
        (signed r (axisY horizontal e)).natAbs = 1 := by
      cases h : horizontal e <;> cases r <;> simp [axisX, axisY, signed, h]
    simp only [displacement, length, edges, List.length_cons] at *
    omega

end Walk

section Relation

variable {m : ℕ} (a b : ZMod m) (source target : E → ZMod m)
    (hstep : ∀ e, target e - source e = if horizontal e then a else b)

include hstep

theorem signed_step (e : E) (r : Bool) :
    a * (signed r (axisX horizontal e) : ZMod m) +
      b * (signed r (axisY horizontal e) : ZMod m) =
        stepTarget source target e r - stepSource source target e r := by
  have hh := hstep e
  cases h : horizontal e <;> cases r <;>
    simp [axisX, axisY, signed, stepSource, stepTarget, h] at * <;>
    first | linear_combination hh | linear_combination -hh

theorem Walk.displacement_relation {u v : ZMod m} (p : Walk source target u v) :
    a * ((p.displacement horizontal).1 : ZMod m) +
      b * ((p.displacement horizontal).2 : ZMod m) = v - u := by
  induction p with
  | nil => simp [Walk.displacement]
  | cons e r p ih =>
    simp only [Walk.displacement, Int.cast_add]
    have hs := signed_step horizontal a b source target hstep e r
    calc
      _ = (a * (signed r (axisX horizontal e) : ZMod m) +
            b * (signed r (axisY horizontal e) : ZMod m)) +
          (a * ((p.displacement horizontal).1 : ZMod m) +
            b * ((p.displacement horizontal).2 : ZMod m)) := by ring
      _ = _ := by rw [hs, ih]; abel

theorem exists_short_relation [DecidableEq E] (S : Finset E)
    (hc : IsCycle source target S) (hl : ∑ e ∈ S, axisLabel horizontal e ≠ 0) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ a * (u : ZMod m) + b * (v : ZMod m) = 0 ∧
      u.natAbs + v.natAbs ≤ S.card := by
  classical
  obtain ⟨w, p, hn, hs, hlp⟩ := detected_closed_trail source target (axisLabel horizontal) S hc hl
  refine ⟨(p.displacement horizontal).1, (p.displacement horizontal).2, ?_, ?_, ?_⟩
  · by_contra h
    simp only [not_or, not_not] at h
    apply hlp
    rw [p.label_sum horizontal, h.1, h.2]
    rfl
  · simpa using p.displacement_relation horizontal a b source target hstep
  · exact (p.displacement_norm_le horizontal).trans (p.length_le_card S hn hs)

end Relation

section BinarySupport

open Matrix

variable [Fintype E] [DecidableEq E]

def binarySupport (x : E → ZMod 2) : Finset E := Finset.univ.filter fun e => x e ≠ 0

theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

omit [DecidableEq E] in
theorem sum_support_eq_dot (x f : E → ZMod 2) :
    ∑ e ∈ binarySupport x, f e = x ⬝ᵥ f := by
  rw [binarySupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rcases binary_cases (x e) with h | h <;> simp [h]

omit [DecidableEq E] in
theorem cycle_of_kernel [Fintype V] [DecidableEq V]
    (H : Matrix V E (ZMod 2))
    (hH : ∀ v e, H v e = incidence source target e v)
    (x : E → ZMod 2) (hx : H.mulVec x = 0) : IsCycle source target (binarySupport x) := by
  intro v
  rw [sum_support_eq_dot, dotProduct_comm]
  simpa only [← hH] using congrFun hx v

omit [DecidableEq E] in
theorem label_sum_ne_zero_of_pairing (x : E → ZMod 2) (detectors : Fin 2 → E → ZMod 2)
    (h0 : ∀ e, detectors 0 e = (axisLabel horizontal e).1)
    (h1 : ∀ e, detectors 1 e = (axisLabel horizontal e).2)
    (hp : ∃ j, x ⬝ᵥ detectors j = 1) : ∑ e ∈ binarySupport x, axisLabel horizontal e ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hp
  have hf := congrArg Prod.fst hz
  have hs := congrArg Prod.snd hz
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero] at hf hs
  simp_rw [← h0] at hf
  simp_rw [← h1] at hs
  rw [sum_support_eq_dot] at hf hs
  fin_cases j <;> simp_all

theorem weight_ge_of_lattice_bound {m : ℕ} (a b : ZMod m)
    (source target : E → ZMod m)
    (hstep : ∀ e, target e - source e = if horizontal e then a else b)
    (D : ℕ)
    (hbound : ∀ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) →
      a * (u : ZMod m) + b * (v : ZMod m) = 0 → D ≤ u.natAbs + v.natAbs)
    (x : E → ZMod 2) (hc : IsCycle source target (binarySupport x))
    (hl : ∑ e ∈ binarySupport x, axisLabel horizontal e ≠ 0) : D ≤ hammingNorm x := by
  obtain ⟨u, v, hn, he, hw⟩ := exists_short_relation horizontal a b source target hstep _ hc hl
  exact (hbound u v hn he).trans hw

end BinarySupport
end QldpcVerification.Lattice
