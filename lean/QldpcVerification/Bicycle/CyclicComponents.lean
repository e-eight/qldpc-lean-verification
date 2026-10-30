import QldpcVerification.Bicycle.JointCoverage
import QldpcVerification.Components

/-! Residue classes of a common cyclic divisor give explicit independent components. -/

namespace QldpcVerification.Bicycle.Decomposition

open Matrix Module

variable (c l : ℕ) [NeZero c] [NeZero l]

def vertex (r : Fin c) (v : ZMod l) : ZMod (c * l) := (r.val + c * v.val : ℕ)

theorem vertex_val (r : Fin c) (v : ZMod l) : (vertex c l r v).val = r.val + c * v.val := by
  have hc := Nat.pos_of_ne_zero (NeZero.ne c)
  have hv := v.val_lt
  have hr := r.isLt
  apply ZMod.val_natCast_of_lt
  nlinarith

theorem vertex_injective : Function.Injective (fun q : Fin c × ZMod l => vertex c l q.1 q.2) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have he := congrArg ZMod.val h
  rw [vertex_val, vertex_val] at he
  change i.val + c * u.val = j.val + c * v.val at he
  have hr : i.val = j.val := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using
      congrArg (fun n : ℕ => n % c) he
  have hv : u.val = v.val := by
    have hm : c * u.val = c * v.val := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne c)) hm
  exact Prod.ext (Fin.ext hr) (ZMod.val_injective l hv)

theorem vertex_surjective : Function.Surjective (fun q : Fin c × ZMod l => vertex c l q.1 q.2) := by
  intro v
  have hc := Nat.pos_of_ne_zero (NeZero.ne c)
  have hl : v.val / c < l := (Nat.div_lt_iff_lt_mul hc).mpr (by simpa [Nat.mul_comm] using v.val_lt)
  refine ⟨(⟨v.val % c, Nat.mod_lt _ hc⟩, (v.val / c : ZMod l)), ?_⟩
  simp [vertex, ZMod.val_natCast_of_lt hl, Nat.mod_add_div]

noncomputable def vertices : Fin c × ZMod l ≃ ZMod (c * l) :=
  Equiv.ofBijective _ ⟨vertex_injective c l, vertex_surjective c l⟩

omit [NeZero c] [NeZero l] in
theorem scaled_mod (n : ℕ) :
    (c : ZMod (c * l)) * ((n % l : ℕ) : ZMod (c * l)) =
      (c : ZMod (c * l)) * (n : ZMod (c * l)) := by
  have hz : (c : ZMod (c * l)) * (l : ZMod (c * l)) = 0 := by
    rw [← Nat.cast_mul]
    exact ZMod.natCast_self _
  have h := congrArg (fun k : ℕ => (c : ZMod (c * l)) * (k : ZMod (c * l))) (Nat.mod_add_div n l)
  simpa [Nat.cast_add, Nat.cast_mul, mul_add, ← mul_assoc, hz] using h

theorem vertex_add (r : Fin c) (v : ZMod l) (a : ℕ) :
    vertex c l r (v + (a : ZMod l)) = vertex c l r v + (c * a : ℕ) := by
  have he : v + (a : ZMod l) = ((v.val + a : ℕ) : ZMod l) := by simp
  unfold vertex
  rw [he, ZMod.val_natCast]
  simp only [Nat.cast_add, Nat.cast_mul]
  rw [scaled_mod]
  push_cast
  ring

noncomputable def edges : Fin c × Connected.Edge l ≃ Connected.Edge (c * l) :=
  (Equiv.prodSumDistrib _ _ _).trans (Equiv.sumCongr (vertices c l) (vertices c l))

@[simp] theorem edges_inl (r : Fin c) (v : ZMod l) :
    edges c l (r, Sum.inl v) = Sum.inl (vertex c l r v) := rfl

@[simp] theorem edges_inr (r : Fin c) (v : ZMod l) :
    edges c l (r, Sum.inr v) = Sum.inr (vertex c l r v) := rfl

theorem source_edges (q : Fin c × Connected.Edge l) :
    Connected.source (edges c l q) = vertices c l (q.1, Connected.source q.2) := by
  rcases q with ⟨r, e⟩
  cases e <;> rfl

theorem target_edges (a b : ℕ) (q : Fin c × Connected.Edge l) :
    Connected.target (c * a) (c * b) (edges c l q) =
      vertices c l (q.1, Connected.target a b q.2) := by
  rcases q with ⟨r, e⟩
  cases e <;> exact (vertex_add c l r _ _).symm

theorem pull_H (a b : ℕ) (r : Fin c × ZMod l) :
    pull (edges c l) (Connected.H (c * a) (c * b) (vertices c l r)) =
      Components.block (Connected.H a b) r := by
  funext q
  change Lattice.incidence Connected.source (Connected.target (c * a) (c * b))
    (edges c l q) (vertices c l r) = _
  simp only [Lattice.incidence, source_edges, target_edges, (vertices c l).injective.eq_iff]
  rcases q with ⟨i, e⟩
  rcases r with ⟨j, v⟩
  by_cases h : i = j
  · subst j
    simp [Components.block, Connected.H, Lattice.incidence]
  · simp [Components.block, h, Ne.symm h]

theorem pull_single {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (v : A) : pull e (Pi.single (e v) (1 : ZMod 2)) = Pi.single v 1 := by
  ext w
  simp [pull, Pi.single_apply, e.injective.eq_iff]

theorem pull_F (a b : ℕ) (r : Fin c × ZMod l) :
    pull (edges c l) (Connected.F (c * a) (c * b) (vertices c l r)) =
      Components.block (Connected.F a b) r := by
  rcases r with ⟨i, v⟩
  rw [Connected.face_explicit]
  change pull (edges c l) (Pi.single (edges c l (i, Sum.inl v)) 1 +
    Pi.single (Sum.inr (vertex c l i v + (c * a : ℕ))) 1 +
    Pi.single (Sum.inl (vertex c l i v + (c * b : ℕ))) 1 +
    Pi.single (edges c l (i, Sum.inr v)) 1) = _
  rw [← vertex_add c l i v a, ← vertex_add c l i v b]
  change pull (edges c l) (Pi.single (edges c l (i, Sum.inl v)) 1 +
    Pi.single (edges c l (i, Sum.inr (v + (a : ZMod l)))) 1 +
    Pi.single (edges c l (i, Sum.inl (v + (b : ZMod l)))) 1 +
    Pi.single (edges c l (i, Sum.inr v)) 1) = _
  simp only [map_add, pull_single]
  funext ⟨j, e⟩
  by_cases h : i = j
  · subst j
    simp [Components.block, Connected.face_explicit, Pi.single_apply]
  · simp [Components.block, h, Ne.symm h]

end QldpcVerification.Bicycle.Decomposition
