import QldpcVerification.Bicycle.PeriodBasis

/-! Walks with prescribed signed displacement in the original two edge directions. -/

namespace QldpcVerification.Lattice.Walk

variable {E V : Type} {source target : E → V}

def reverse : {u v : V} → Walk source target u v → Walk source target v u
  | _, _, .nil v => .nil v
  | _, _, .cons e r w => (reverse w).append
      ((single e (!r)).copy (by cases r <;> rfl) (by cases r <;> rfl))

@[simp] theorem displacement_reverse (horizontal : E → Bool) {u v : V}
    (w : Walk source target u v) :
    w.reverse.displacement horizontal = -w.displacement horizontal := by
  induction w with
  | nil => simp [reverse, displacement]
  | cons e r w ih =>
    rw [reverse, displacement_append, displacement_copy, ih]
    apply Prod.ext <;> cases r <;>
      simp [single, displacement, signed, axisX, axisY]

end QldpcVerification.Lattice.Walk

namespace QldpcVerification.Bicycle.Connected

open Lattice

variable {m : ℕ} [NeZero m]

def horizontalPath (s t : ℕ) : (n : ℕ) → (v : ZMod m) →
    Walk source (target s t) v (v + (n : ZMod m) * (s : ZMod m))
  | 0, v => (Walk.nil v).copy rfl (by simp)
  | n + 1, v => ((hEdge s t v).append (horizontalPath s t n (v + (s : ZMod m)))).copy
      rfl (by push_cast; ring)

def verticalPath (s t : ℕ) : (n : ℕ) → (v : ZMod m) →
    Walk source (target s t) v (v + (n : ZMod m) * (t : ZMod m))
  | 0, v => (Walk.nil v).copy rfl (by simp)
  | n + 1, v => ((vEdge s t v).append (verticalPath s t n (v + (t : ZMod m)))).copy
      rfl (by push_cast; ring)

theorem horizontalPath_displacement (s t n : ℕ) (v : ZMod m) :
    (horizontalPath s t n v).displacement Normalized.horizontal = ((n : ℤ), 0) := by
  induction n generalizing v with
  | zero => simp [horizontalPath, Walk.displacement]
  | succ n ih =>
    simp [horizontalPath, ih, hEdge, Walk.single, Walk.displacement,
      Normalized.horizontal, axisX, axisY, signed, add_comm]

theorem verticalPath_displacement (s t n : ℕ) (v : ZMod m) :
    (verticalPath s t n v).displacement Normalized.horizontal = (0, (n : ℤ)) := by
  induction n generalizing v with
  | zero => simp [verticalPath, Walk.displacement]
  | succ n ih =>
    simp [verticalPath, ih, vEdge, Walk.single, Walk.displacement,
      Normalized.horizontal, axisX, axisY, signed, add_comm]

def horizontalIntPath (s t : ℕ) (u : ℤ) (v : ZMod m) :
    Walk source (target s t) v (v + (u : ZMod m) * (s : ZMod m)) :=
  match u with
  | .ofNat n => (horizontalPath s t n v).copy rfl (by simp)
  | .negSucc n =>
      (horizontalPath s t (n + 1) (v - ((n + 1 : ℕ) : ZMod m) * (s : ZMod m))).reverse.copy
        (by ring) (by simp; ring)

def verticalIntPath (s t : ℕ) (u : ℤ) (v : ZMod m) :
    Walk source (target s t) v (v + (u : ZMod m) * (t : ZMod m)) :=
  match u with
  | .ofNat n => (verticalPath s t n v).copy rfl (by simp)
  | .negSucc n =>
      (verticalPath s t (n + 1) (v - ((n + 1 : ℕ) : ZMod m) * (t : ZMod m))).reverse.copy
        (by ring) (by simp; ring)

theorem horizontalIntPath_displacement (s t : ℕ) (u : ℤ) (v : ZMod m) :
    (horizontalIntPath s t u v).displacement Normalized.horizontal = (u, 0) := by
  cases u <;> simp [horizontalIntPath, horizontalPath_displacement] <;> omega

theorem verticalIntPath_displacement (s t : ℕ) (u : ℤ) (v : ZMod m) :
    (verticalIntPath s t u v).displacement Normalized.horizontal = (0, u) := by
  cases u <;> simp [verticalIntPath, verticalPath_displacement] <;> omega

def displacementPath (s t : ℕ) (u v : ℤ) : Walk (source (m := m)) (target s t) 0
    ((u : ZMod m) * (s : ZMod m) + (v : ZMod m) * (t : ZMod m)) :=
  ((horizontalIntPath s t u 0).append
    (verticalIntPath s t v (0 + (u : ZMod m) * (s : ZMod m)))).copy rfl (by simp)

theorem displacementPath_displacement (s t : ℕ) (u v : ℤ) :
    (displacementPath (m := m) s t u v).displacement Normalized.horizontal = (u, v) := by
  simp [displacementPath, horizontalIntPath_displacement, verticalIntPath_displacement]

def closedPath (s t : ℕ) (u v : ℤ)
    (h : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0) :
    Walk (source (m := m)) (target s t) 0 0 :=
  (displacementPath s t u v).copy rfl (by simpa only [mul_comm] using h)

@[simp] theorem closedPath_displacement (s t : ℕ) (u v : ℤ)
    (h : (s : ZMod m) * (u : ZMod m) + (t : ZMod m) * (v : ZMod m) = 0) :
    (closedPath s t u v h).displacement Normalized.horizontal = (u, v) := by
  simp [closedPath, displacementPath_displacement]

end QldpcVerification.Bicycle.Connected
