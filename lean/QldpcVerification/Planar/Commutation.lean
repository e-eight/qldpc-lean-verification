import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Commutation of the explicit rectangular 722-qubit model

The matrices below implement the definition in `analytical/planar722/DRAFT.typ`.
`false` is species A, `true` is species B. Coordinates are ordinary integers,
not periodic coordinates. Restriction to the board is built into `atom`.

The proof interchanges two three-term sums, rather than evaluating the
357 by 357 matrix product. `finite_overlap` is the finite-support convolution
step: an intersection contributes once, and the strip bounds ensure that
every possible intersection is retained on the board.

This source and its guarded audit await detached, capped Lean replay.
It does not identify the matrices with an external JSON input or establish
ranks, distance, or verification of the whole draft.
-/

namespace QldpcVerification.Planar.Commutation

abbrev F2 := ZMod 2
abbrev Cell := Fin 19 × Fin 19
abbrev Q := Bool × Cell
abbrev XAnchor := Fin 21 × Fin 17
abbrev ZAnchor := Fin 17 × Fin 21
abbrev Lattice := ℤ × ℤ

def cell (q : Cell) : Lattice := (q.1.val, q.2.val)
def xAnchor (a : XAnchor) : Lattice := ((a.1.val : ℤ) - 2, a.2.val)
def zAnchor (c : ZAnchor) : Lattice := ((c.1.val : ℤ) + 2, c.2.val)

/-- Exponents of `f = x + x² + y²`. -/
def fShift : Fin 3 → Lattice := ![(1, 0), (2, 0), (0, 2)]
/-- Exponents of `g = 1 + x²y + x²y²`. -/
def gShift : Fin 3 → Lattice := ![(0, 0), (2, 1), (2, 2)]

/-- A lattice monomial, restricted to the physical board. -/
def atom (p : Lattice) (q : Cell) : F2 := if cell q = p then 1 else 0

def xBlock (a : XAnchor) (s : Fin 3 → Lattice) (q : Cell) : F2 :=
  ∑ i, atom (xAnchor a + s i) q

def zBlock (c : ZAnchor) (s : Fin 3 → Lattice) (q : Cell) : F2 :=
  ∑ i, atom (zAnchor c - s i) q

/-- Explicit finite X matrix; anchor `(a,b)` represents `(a-2,b)`. -/
def HX : Matrix XAnchor Q F2 := fun a q =>
  if q.1 then xBlock a gShift q.2 else xBlock a fShift q.2

/-- Explicit finite Z matrix; anchor `(c,d)` represents `(c+2,d)`. -/
def HZ : Matrix ZAnchor Q F2 := fun c q =>
  if q.1 then zBlock c fShift q.2 else zBlock c gShift q.2

theorem cell_injective : Function.Injective cell := by
  intro q r h
  apply Prod.ext
  · apply Fin.ext
    have he := congrArg Prod.fst h
    simpa [cell] using he
  · apply Fin.ext
    have he := congrArg Prod.snd h
    simpa [cell] using he

/-- A symbolic delta-function overlap, assuming no common point is discarded. -/
theorem finite_overlap (u v : Lattice)
    (hboard : u = v → ∃ q : Cell, cell q = u) :
    (∑ q : Cell, atom u q * atom v q) = if u = v then 1 else 0 := by
  classical
  by_cases huv : u = v
  · subst v
    obtain ⟨q, hq⟩ := hboard rfl
    simp only [atom, ← hq, cell_injective.eq_iff]
    simp
  · rw [if_neg huv]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hu : cell q = u
    · have hv : cell q ≠ v := fun hv => huv (hu.symm.trans hv)
      simp [atom, hu, hv, huv]
    · simp [atom, hu, huv]

/-- Each exponent of either polynomial lies in `[0,2]²`. -/
def Small (s : Fin 3 → Lattice) : Prop :=
  ∀ i, 0 ≤ (s i).1 ∧ (s i).1 ≤ 2 ∧ 0 ≤ (s i).2 ∧ (s i).2 ≤ 2

theorem fShift_small : Small fShift := by
  intro i
  fin_cases i <;> norm_num [fShift]

theorem gShift_small : Small gShift := by
  intro i
  fin_cases i <;> norm_num [gShift]

/-- X rows remain inside the horizontal strip, including before truncation. -/
theorem x_strip (a : XAnchor) (s : Fin 3 → Lattice) (hs : Small s) (i : Fin 3) :
    0 ≤ (xAnchor a + s i).2 ∧ (xAnchor a + s i).2 ≤ 18 := by
  have hi := hs i
  have ha := a.2.isLt
  change 0 ≤ (a.2.val : ℤ) + (s i).2 ∧ (a.2.val : ℤ) + (s i).2 ≤ 18
  omega

/-- Z rows remain inside the vertical strip, including before truncation. -/
theorem z_strip (c : ZAnchor) (s : Fin 3 → Lattice) (hs : Small s) (i : Fin 3) :
    0 ≤ (zAnchor c - s i).1 ∧ (zAnchor c - s i).1 ≤ 18 := by
  have hi := hs i
  have hc := c.1.isLt
  change 0 ≤ (c.1.val : ℤ) + 2 - (s i).1 ∧
    (c.1.val : ℤ) + 2 - (s i).1 ≤ 18
  omega

/-- The two strip bounds imply that truncation removes no intersection. -/
theorem intersection_on_board (a : XAnchor) (c : ZAnchor)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) (i j : Fin 3)
    (h : xAnchor a + s i = zAnchor c - t j) :
    ∃ q : Cell, cell q = xAnchor a + s i := by
  have hy := x_strip a s hs i
  have hx := z_strip c t ht j
  rw [← h] at hx
  let p := xAnchor a + s i
  have hx' : 0 ≤ p.1 ∧ p.1 ≤ 18 := hx
  have hy' : 0 ≤ p.2 ∧ p.2 ≤ 18 := hy
  refine ⟨(⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩), ?_⟩
  apply Prod.ext
  · change (p.1.toNat : ℤ) = p.1
    exact Int.toNat_of_nonneg hx'.1
  · change (p.2.toNat : ℤ) = p.2
    exact Int.toNat_of_nonneg hy'.1

/-- Interchange the sums with abstract index types, so no concrete board is reduced. -/
theorem sum_pairing {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (u : I → K → F2) (v : J → K → F2) (w : I → J → F2)
    (h : ∀ i j, (∑ q : K, u i q * v j q) = w i j) :
    (∑ q : K, (∑ i : I, u i q) * (∑ j : J, v j q)) =
      ∑ i : I, ∑ j : J, w i j := by
  classical
  simp only [Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact h i j

/-- The finite-board overlap is precisely the sparse convolution coefficient. -/
theorem block_overlap (a : XAnchor) (c : ZAnchor)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) :
    (∑ q : Cell, xBlock a s q * zBlock c t q) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (if xAnchor a + s i = zAnchor c - t j then 1 else 0 : F2) := by
  exact sum_pairing
    (fun i q => atom (xAnchor a + s i) q)
    (fun j q => atom (zAnchor c - t j) q)
    (fun i j => if xAnchor a + s i = zAnchor c - t j then 1 else 0)
    (fun i j => finite_overlap (xAnchor a + s i) (zAnchor c - t j)
      (intersection_on_board a c s t hs ht i j))

set_option maxRecDepth 2000 in
/-- Commutativity of convolution, expressed as equality of the two block overlaps. -/
theorem block_overlap_swap (a : XAnchor) (c : ZAnchor)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) :
    (∑ q : Cell, xBlock a s q * zBlock c t q) =
      ∑ q : Cell, xBlock a t q * zBlock c s q := by
  classical
  rw [block_overlap a c s t hs ht, block_overlap a c t s ht hs]
  rw [Finset.sum_comm (f := fun j i =>
    (if xAnchor a + t j = zAnchor c - s i then 1 else 0 : F2))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : xAnchor a + s i = zAnchor c - t j ↔
      xAnchor a + t j = zAnchor c - s i := by
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
    constructor <;> intro h <;>
      simpa only [add_assoc, add_comm, add_left_comm] using h
  simp only [he]

/-- Every actual finite X row is orthogonal to every actual finite Z row. -/
theorem rows_orthogonal (a : XAnchor) (c : ZAnchor) :
    (∑ q : Q, HX a q * HZ c q) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, HX, HZ, Bool.false_eq_true, if_false, if_true]
  rw [block_overlap_swap a c gShift fShift gShift_small fShift_small]
  have htwo : (2 : F2) = 0 := by decide
  rw [← two_mul, htwo, zero_mul]

/-- Finite `357 × 722` matrices commute; no exhaustive anchor evaluation is used. -/
theorem commutation : HX * HZ.transpose = 0 := by
  ext a c
  change (∑ q : Q, HX a q * HZ c q) = 0
  exact rows_orthogonal a c

end QldpcVerification.Planar.Commutation
