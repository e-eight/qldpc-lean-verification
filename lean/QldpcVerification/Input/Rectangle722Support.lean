import QldpcVerification.Rectangle722

/-! Generated symbolic sparse-row bridge. No enumeration of qubits or errors. -/
namespace QldpcVerification.Input.Rectangle722Recognition

open Planar.Commutation

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- A clipped monomial, in the existing physical qubit numbering. -/
def point (b : Bool) (p : Lattice) : Multiset (Fin 722) :=
  if h : 0 ≤ p.1 ∧ p.1 < 19 ∧ 0 ≤ p.2 ∧ p.2 < 19 then
    {Rectangle722.qubits (b, (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩))}
  else 0

/-- Sparse row semantics: sum of singleton indicators over F₂. -/
def row (s : Multiset (Fin 722)) (q : Fin 722) : F2 :=
  (s.map (fun r => if q = r then (1 : F2) else 0)).sum

@[simp] theorem row_add (s t : Multiset (Fin 722)) (q : Fin 722) :
    row (s + t) q = row s q + row t q := by
  simp [row, Multiset.map_add]

/-- The generic indicator bridge, including points discarded at the boundary. -/
theorem point_row (b : Bool) (p : Lattice) (q : Q) :
    row (point b p) (Rectangle722.qubits q) =
      if q.1 = b then atom p q.2 else 0 := by
  unfold point
  split
  · rename_i h
    let c : Cell := (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩)
    have hc : cell c = p := by
      apply Prod.ext <;> simp [cell, c, h.1, h.2.2.1]
    have he : q = (b, c) ↔ q.1 = b ∧ cell q.2 = p := by
      constructor
      · intro hq
        subst q
        exact ⟨rfl, hc⟩
      · rintro ⟨hb, hp⟩
        exact Prod.ext hb (cell_injective (hp.trans hc.symm))
    change row {Rectangle722.qubits (b, c)} (Rectangle722.qubits q) = _
    simp only [row, Multiset.map_singleton, Multiset.sum_singleton,
      Rectangle722.qubits.injective.eq_iff, he, atom]
    split_ifs <;> simp_all
  · rename_i h
    have hp : cell q.2 ≠ p := by
      intro hp
      have hx := q.2.1.isLt
      have hy := q.2.2.isLt
      have hx' := congrArg Prod.fst hp
      have hy' := congrArg Prod.snd hp
      simp only [cell] at hx' hy'
      omega
    simp [row, atom, hp]

/-- Six translated terms before boundary truncation. -/
def expectedX (a : XAnchor) : Multiset (Fin 722) :=
  point false (xAnchor a + fShift 0) +
  point false (xAnchor a + fShift 1) +
  point false (xAnchor a + fShift 2) +
  point true (xAnchor a + gShift 0) +
  point true (xAnchor a + gShift 1) +
  point true (xAnchor a + gShift 2)

def expectedZ (c : ZAnchor) : Multiset (Fin 722) :=
  point false (zAnchor c - gShift 0) +
  point false (zAnchor c - gShift 1) +
  point false (zAnchor c - gShift 2) +
  point true (zAnchor c - fShift 0) +
  point true (zAnchor c - fShift 1) +
  point true (zAnchor c - fShift 2)

/-- Symbolic in both anchor and qubit; only the three polynomial terms expand. -/
theorem expectedX_row (a : XAnchor) (q : Q) :
    row (expectedX a) (Rectangle722.qubits q) = HX a q := by
  rcases q with ⟨b, q⟩
  cases b <;>
    simp [expectedX, row_add, point_row, HX, xBlock, Fin.sum_univ_succ, add_assoc]

theorem expectedZ_row (c : ZAnchor) (q : Q) :
    row (expectedZ c) (Rectangle722.qubits q) = HZ c q := by
  rcases q with ⟨b, q⟩
  cases b <;>
    simp [expectedZ, row_add, point_row, HZ, zBlock, Fin.sum_univ_succ, add_assoc]

end QldpcVerification.Input.Rectangle722Recognition
