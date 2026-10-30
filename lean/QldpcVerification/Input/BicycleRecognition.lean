import QldpcVerification.Bicycle.Normalization
import QldpcVerification.Input.SparseCertificates

/-! Sparse recognition of binomial rows. Only four-point supports and their
distinctness need finite evaluation; no dense matrix equality is evaluated.
-/

namespace QldpcVerification.Input.BicycleRecognition

open Matrix Bicycle Normalization Normalized Sparse

variable {m : ℕ} [NeZero m]

def hPoints (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) : List (Edge m) :=
  [.inl (v + r), .inl (v + r - u), .inr (v + s), .inr (v + s - (u : ZMod m) * (a : ZMod m))]

def fPoints (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) : List (Edge m) :=
  [.inl (v - s), .inr (v - r + u), .inl (v - s + (u : ZMod m) * (a : ZMod m)), .inr (v - r)]

omit [NeZero m] in
theorem hPoints_sum (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) :
    ((hPoints u r s a v).map (fun e => Pi.single e (1 : ZMod 2))).sum = rawH u r s a v := by
  simp [hPoints, rawH, add_assoc]

omit [NeZero m] in
theorem fPoints_sum (u : (ZMod m)ˣ) (r s : ZMod m) (a : ℕ) (v : ZMod m) :
    ((fPoints u r s a v).map (fun e => Pi.single e (1 : ZMod 2))).sum = rawF u r s a v := by
  simp [fPoints, rawF, add_assoc]

theorem indicator_list {n : ℕ} (l : List (Fin n)) (hn : l.Nodup) :
    indicator l.toFinset = (l.map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  induction l with
  | nil => funext q; simp [indicator]
  | cons p l ih =>
    have hp : p ∉ l.toFinset := by simpa using (List.nodup_cons.mp hn).1
    rw [List.map_cons, List.sum_cons, ← ih (List.nodup_cons.mp hn).2]
    funext q
    by_cases hq : q = p
    · subst q
      simp [indicator, hp]
    · simp [indicator, hq]

theorem pull_points {E : Type} [DecidableEq E] {n : ℕ}
    (qubits : E ≃ Fin n) (l : List E) :
    pull qubits (((l.map qubits).map (fun q => Pi.single q (1 : ZMod 2))).sum) =
      (l.map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, map_add, pull_single_image, ih]

theorem row_of_points {E : Type} [DecidableEq E] {n : ℕ}
    (qubits : E ≃ Fin n) (row : Finset (Fin n)) (l : List E)
    (hr : row = (l.map qubits).toFinset) (hn : (l.map qubits).Nodup) :
    pull qubits (indicator row) = (l.map (fun q => Pi.single q (1 : ZMod 2))).sum := by
  rw [hr, indicator_list _ hn, pull_points]

end QldpcVerification.Input.BicycleRecognition
