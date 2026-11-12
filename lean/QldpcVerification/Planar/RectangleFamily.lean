import QldpcVerification.Planar.BoundaryRecurrence
import QldpcVerification.Input.Homological
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The open rectangular polynomial-code family

The side lengths are `m + 2` and `n + 2`, where `m,n` can be zero.
The two checks have ranks `(m + 4) * n` and `m * (n + 4)` and encode eight
qubits. Sparse convolution proves commutation. Polynomial recurrence
injectivity proves row independence without evaluating finite matrices.
-/

namespace QldpcVerification.Planar.RectangleFamily

open Polynomial

abbrev F2 := ZMod 2
abbrev Cell (m n : ℕ) := Fin (m + 2) × Fin (n + 2)
abbrev Q (m n : ℕ) := Bool × Cell m n
abbrev XAnchor (m n : ℕ) := Fin (m + 4) × Fin n
abbrev ZAnchor (m n : ℕ) := Fin m × Fin (n + 4)
abbrev Lattice := ℤ × ℤ

variable {m n : ℕ}

def cell (q : Cell m n) : Lattice := (q.1.val, q.2.val)
def xAnchor (a : XAnchor m n) : Lattice := ((a.1.val : ℤ) - 2, a.2.val)
def zAnchor (c : ZAnchor m n) : Lattice := ((c.1.val : ℤ) + 2, c.2.val)

/-- Exponents of `f = x + x² + y²`. -/
def fShift : Fin 3 → Lattice := ![(1, 0), (2, 0), (0, 2)]
/-- Exponents of `g = 1 + x²y + x²y²`. -/
def gShift : Fin 3 → Lattice := ![(0, 0), (2, 1), (2, 2)]

/-- A lattice monomial, restricted to the physical board. -/
def atom (p : Lattice) (q : Cell m n) : F2 := if cell q = p then 1 else 0

def xBlock (a : XAnchor m n) (s : Fin 3 → Lattice) (q : Cell m n) : F2 :=
  ∑ i, atom (xAnchor a + s i) q

def zBlock (c : ZAnchor m n) (s : Fin 3 → Lattice) (q : Cell m n) : F2 :=
  ∑ i, atom (zAnchor c - s i) q

/-- Explicit finite X matrix; anchor `(a,b)` represents `(a-2,b)`. -/
def HX (m n : ℕ) : Matrix (XAnchor m n) (Q m n) F2 := fun a q =>
  if q.1 then xBlock a gShift q.2 else xBlock a fShift q.2

/-- Explicit finite Z matrix; anchor `(c,d)` represents `(c+2,d)`. -/
def HZ (m n : ℕ) : Matrix (ZAnchor m n) (Q m n) F2 := fun c q =>
  if q.1 then zBlock c fShift q.2 else zBlock c gShift q.2

theorem cell_injective : Function.Injective (cell (m := m) (n := n)) := by
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
    (hboard : u = v → ∃ q : Cell m n, cell q = u) :
    (∑ q : Cell m n, atom u q * atom v q) = if u = v then 1 else 0 := by
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
theorem x_strip (a : XAnchor m n) (s : Fin 3 → Lattice) (hs : Small s) (i : Fin 3) :
    0 ≤ (xAnchor a + s i).2 ∧ (xAnchor a + s i).2 ≤ (n : ℤ) + 1 := by
  have hi := hs i
  have ha := a.2.isLt
  change 0 ≤ (a.2.val : ℤ) + (s i).2 ∧ (a.2.val : ℤ) + (s i).2 ≤ (n : ℤ) + 1
  omega

/-- Z rows remain inside the vertical strip, including before truncation. -/
theorem z_strip (c : ZAnchor m n) (s : Fin 3 → Lattice) (hs : Small s) (i : Fin 3) :
    0 ≤ (zAnchor c - s i).1 ∧ (zAnchor c - s i).1 ≤ (m : ℤ) + 1 := by
  have hi := hs i
  have hc := c.1.isLt
  change 0 ≤ (c.1.val : ℤ) + 2 - (s i).1 ∧
    (c.1.val : ℤ) + 2 - (s i).1 ≤ (m : ℤ) + 1
  omega

/-- The two strip bounds imply that truncation removes no intersection. -/
theorem intersection_on_board (a : XAnchor m n) (c : ZAnchor m n)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) (i j : Fin 3)
    (h : xAnchor a + s i = zAnchor c - t j) :
    ∃ q : Cell m n, cell q = xAnchor a + s i := by
  have hy := x_strip a s hs i
  have hx := z_strip c t ht j
  rw [← h] at hx
  let p := xAnchor a + s i
  have hx' : 0 ≤ p.1 ∧ p.1 ≤ (m : ℤ) + 1 := hx
  have hy' : 0 ≤ p.2 ∧ p.2 ≤ (n : ℤ) + 1 := hy
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
theorem block_overlap (a : XAnchor m n) (c : ZAnchor m n)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) :
    (∑ q : Cell m n, xBlock a s q * zBlock c t q) =
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
theorem block_overlap_swap (a : XAnchor m n) (c : ZAnchor m n)
    (s t : Fin 3 → Lattice) (hs : Small s) (ht : Small t) :
    (∑ q : Cell m n, xBlock a s q * zBlock c t q) =
      ∑ q : Cell m n, xBlock a t q * zBlock c s q := by
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
theorem rows_orthogonal (a : XAnchor m n) (c : ZAnchor m n) :
    (∑ q : Q m n, HX m n a q * HZ m n c q) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, HX, HZ, Bool.false_eq_true, if_false, if_true]
  rw [block_overlap_swap a c gShift fShift gShift_small fShift_small]
  have htwo : (2 : F2) = 0 := by decide
  rw [← two_mul, htwo, zero_mul]

/-- Every rectangle commutes, including empty X or Z anchor types. -/
theorem commutation (m n : ℕ) : HX m n * (HZ m n).transpose = 0 := by
  ext a c
  change (∑ q : Q m n, HX m n a q * HZ m n c q) = 0
  exact rows_orthogonal a c


/-- Flattening the X anchor array changes no coefficients. -/
def xAnchorCoordinates (m n : ℕ) :
    (XAnchor m n → F2) ≃ₗ[F2] (Fin (m + 4) → Fin n → F2) where
  toFun c i j := c (i, j)
  invFun c a := c a.1 a.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reflection puts the Z anchors into the transverse recurrence orientation. -/
def zAnchorCoordinates (m n : ℕ) :
    (ZAnchor m n → F2) ≃ₗ[F2] (Fin (n + 4) → Fin m → F2) where
  toFun c i j := c (j.rev, i.rev)
  invFun c a := c a.2.rev a.1.rev
  left_inv c := by funext a; simp
  right_inv c := by funext i j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def xPhysicalCoordinates (m n : ℕ) :
    (Fin (m + 2) → Fin (n + 2) → F2 × F2) ≃ₗ[F2] (Q m n → F2) where
  toFun v q := if q.1 then (v q.2.1 q.2.2).2 else (v q.2.1 q.2.2).1
  invFun v i j := (v (false, (i, j)), v (true, (i, j)))
  left_inv _ := rfl
  right_inv v := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> rfl
  map_add' v w := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> rfl
  map_smul' r v := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> rfl

/-- Reflect physical coordinates and exchange the two species. -/
def zPhysicalCoordinates (m n : ℕ) :
    (Fin (n + 2) → Fin (m + 2) → F2 × F2) ≃ₗ[F2] (Q m n → F2) where
  toFun v q := if q.1 then (v q.2.2.rev q.2.1.rev).1
    else (v q.2.2.rev q.2.1.rev).2
  invFun v i j := (v (true, (j.rev, i.rev)), v (false, (j.rev, i.rev)))
  left_inv v := by funext i j; simp
  right_inv v := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> simp
  map_add' v w := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> rfl
  map_smul' r v := by funext q; rcases q with ⟨b, i, j⟩; cases b <;> rfl

noncomputable def xSynthesis (m n : ℕ) : (XAnchor m n → F2) →ₗ[F2] (Q m n → F2) :=
  (xPhysicalCoordinates m n).toLinearMap.comp
    ((BoundaryRecurrence.xPhysical (m + 2) n).comp (xAnchorCoordinates m n).toLinearMap)

noncomputable def zSynthesis (m n : ℕ) : (ZAnchor m n → F2) →ₗ[F2] (Q m n → F2) :=
  (zPhysicalCoordinates m n).toLinearMap.comp
    ((BoundaryRecurrence.zPhysical (n + 2) m).comp (zAnchorCoordinates m n).toLinearMap)

theorem xSynthesis_injective (m n : ℕ) : Function.Injective (xSynthesis m n) :=
  (xPhysicalCoordinates m n).injective.comp
    ((BoundaryRecurrence.xPhysical_injective (by omega) n).comp
      (xAnchorCoordinates m n).injective)

theorem zSynthesis_injective (m n : ℕ) : Function.Injective (zSynthesis m n) :=
  (zPhysicalCoordinates m n).injective.comp
    ((BoundaryRecurrence.zPhysical_injective (by omega) m).comp
      (zAnchorCoordinates m n).injective)

private theorem pack_impulse {N m : ℕ} (a : Fin N × Fin m) (r : F2) (i : Fin N) :
    BoundaryRecurrence.pack N m (fun i j => if (i, j) = a then r else 0) i =
      if i = a.1 then monomial a.2.val r else 0 := by
  classical
  rcases a with ⟨a, b⟩
  by_cases hi : i = a
  · subst i
    simp [BoundaryRecurrence.pack, Prod.mk.injEq, apply_ite]
  · simp [BoundaryRecurrence.pack, Prod.mk.injEq, hi, apply_ite]

private theorem entry_pack_impulse {N m : ℕ} (a : Fin N × Fin m) (r : F2) (k : ℕ) :
    BoundaryRecurrence.entry
      (BoundaryRecurrence.pack N m (fun i j => if (i, j) = a then r else 0)) k =
      if k = a.1.val then monomial a.2.val r else 0 := by
  classical
  unfold BoundaryRecurrence.entry
  split
  · rename_i h
    simpa only [Fin.ext_iff] using pack_impulse a r ⟨k, h⟩
  · rename_i h
    have hk : k ≠ a.1.val := by have := a.1.isLt; omega
    simp [hk]

private noncomputable def pulse {N m : ℕ} (a : Fin N × Fin m) (k : ℕ) : BoundaryRecurrence.P :=
  if k = a.1.val then monomial a.2.val 1 else 0

private theorem pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l : ℕ) :
    (pulse a k).coeff l = if k = a.1.val ∧ a.2.val = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, coeff_monomial]

private theorem X_pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l : ℕ) :
    ((X : BoundaryRecurrence.P) * pulse a k).coeff l =
      if k = a.1.val ∧ a.2.val + 1 = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, X_mul_monomial, coeff_monomial]

private theorem Xpow_pulse_coeff {N m : ℕ} (a : Fin N × Fin m) (k l d : ℕ) :
    ((X : BoundaryRecurrence.P) ^ d * pulse a k).coeff l =
      if k = a.1.val ∧ a.2.val + d = l then 1 else 0 := by
  by_cases h : k = a.1.val <;> simp [pulse, h, X_pow_mul_monomial, coeff_monomial]

private theorem x_impulse_entry (a : XAnchor m n) (k : ℕ) :
    BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1))) k = pulse a k := by
  have hc : xAnchorCoordinates m n (Pi.single a 1) =
      (fun i j => if (i, j) = a then (1 : F2) else 0) := by
    funext i j
    simp [xAnchorCoordinates, Pi.single_apply, eq_comm]
  rw [hc]
  exact entry_pack_impulse a 1 k

private theorem z_impulse_entry (a : ZAnchor m n) (k : ℕ) :
    BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1))) k =
      pulse (a.2.rev, a.1.rev) k := by
  have hc : zAnchorCoordinates m n (Pi.single a 1) =
      (fun i j => if (i, j) = (a.2.rev, a.1.rev) then (1 : F2) else 0) := by
    funext i j
    have he : a = (j.rev, i.rev) ↔ (i, j) = (a.2.rev, a.1.rev) := by
      simp only [Prod.ext_iff]
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using (congrArg Fin.rev h₂).symm,
          by simpa using (congrArg Fin.rev h₁).symm⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨by simpa using (congrArg Fin.rev h₂).symm,
          by simpa using (congrArg Fin.rev h₁).symm⟩
    change (Pi.single a (1 : F2) : ZAnchor m n → F2) (j.rev, i.rev) = _
    have he' : (j.rev, i.rev) = a ↔ (i, j) = (a.2.rev, a.1.rev) := eq_comm.trans he
    simp only [Pi.single_apply, he']
  rw [hc]
  exact entry_pack_impulse (a.2.rev, a.1.rev) 1 k

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- The X synthesis of one anchor is exactly that row of the explicit matrix. -/
theorem xSynthesis_single (a : XAnchor m n) : xSynthesis m n (Pi.single a 1) = HX m n a := by
  funext q
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1))) i.val +
        BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1))) (i.val + 1) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1)))
            (i.val + 2)).coeff j.val = _
    simp only [x_impulse_entry, coeff_add, pulse_coeff, Xpow_pulse_coeff]
    simp only [HX, Bool.false_eq_true, if_false, xBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, fShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change (((X : BoundaryRecurrence.P) + X ^ 2) *
        BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1))) i.val +
        BoundaryRecurrence.entry (BoundaryRecurrence.pack (m + 4) n (xAnchorCoordinates m n (Pi.single a 1)))
          (i.val + 2)).coeff j.val = _
    simp only [x_impulse_entry, add_mul, coeff_add, pulse_coeff,
      X_pulse_coeff, Xpow_pulse_coeff]
    simp only [HX, if_true, xBlock, Fin.sum_univ_succ, Fin.sum_univ_zero,
      gShift, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      atom, cell, xAnchor, Prod.mk_add_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

set_option maxRecDepth 2000 in
set_option maxHeartbeats 800000 in
/-- Reflection and block exchange recover exactly the original Z matrix row. -/
theorem zSynthesis_single (a : ZAnchor m n) : zSynthesis m n (Pi.single a 1) = HZ m n a := by
  funext q
  rcases q with ⟨b, i, j⟩
  have hi := i.isLt
  have hj := j.isLt
  have ha := a.1.isLt
  have hb := a.2.isLt
  cases b
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1)))
          (j.rev.val + 2) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1)))
            (j.rev.val + 1) +
        (X : BoundaryRecurrence.P) ^ 2 *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1)))
            j.rev.val).coeff i.rev.val = _
    simp only [z_impulse_entry, coeff_add, pulse_coeff, Xpow_pulse_coeff,
      Fin.val_rev, Prod.fst, Prod.snd]
    simp only [HZ, Bool.false_eq_true, if_false, zBlock, Fin.sum_univ_succ,
      Fin.sum_univ_zero, gShift, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.head_cons, atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring
  · change (BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1))) j.rev.val +
        ((X : BoundaryRecurrence.P) + X ^ 2) *
          BoundaryRecurrence.entry (BoundaryRecurrence.pack (n + 4) m (zAnchorCoordinates m n (Pi.single a 1)))
            (j.rev.val + 2)).coeff i.rev.val = _
    simp only [z_impulse_entry, add_mul, coeff_add, pulse_coeff,
      X_pulse_coeff, Xpow_pulse_coeff, Fin.val_rev, Prod.fst, Prod.snd]
    simp only [HZ, if_true, zBlock, Fin.sum_univ_succ, Fin.sum_univ_zero,
      fShift, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons,
      atom, cell, zAnchor, Prod.mk_sub_mk, Prod.mk.injEq]
    split_ifs <;> first | omega | ring

/-- Equality of linear maps, not just equality of their ranks. -/
theorem xSynthesis_eq (m n : ℕ) : xSynthesis m n = (HX m n).transpose.mulVecLin := by
  apply (Pi.basisFun F2 (XAnchor m n)).ext
  intro a
  simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.transpose_apply] using xSynthesis_single a

theorem zSynthesis_eq (m n : ℕ) : zSynthesis m n = (HZ m n).transpose.mulVecLin := by
  apply (Pi.basisFun F2 (ZAnchor m n)).ext
  intro a
  simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.transpose_apply] using zSynthesis_single a

/-- Both row ranks, with no positivity assumptions on the interior sizes. -/
theorem matrix_ranks (m n : ℕ) :
    (HX m n).rank = (m + 4) * n ∧ (HZ m n).rank = m * (n + 4) := by
  constructor
  · rw [← Matrix.rank_transpose (HX m n), Matrix.rank, ← xSynthesis_eq,
      LinearMap.finrank_range_of_inj (xSynthesis_injective m n)]
    simp [XAnchor, Module.finrank_pi_fintype]
  · rw [← Matrix.rank_transpose (HZ m n), Matrix.rank, ← zSynthesis_eq,
      LinearMap.finrank_range_of_inj (zSynthesis_injective m n)]
    simp [ZAnchor, Module.finrank_pi_fintype]

abbrev V (m n : ℕ) := Q m n → F2

def SX (m n : ℕ) : Submodule F2 (V m n) :=
  LinearMap.range (HX m n).transpose.mulVecLin

def ZOrthogonal (m n : ℕ) : Submodule F2 (V m n) :=
  LinearMap.ker (HZ m n).mulVecLin

theorem x_mem_zOrthogonal (m n : ℕ) : SX m n ≤ ZOrthogonal m n := by
  apply LinearMap.range_le_ker_iff.mpr
  rw [← Matrix.mulVecLin_mul]
  have h : HZ m n * (HX m n).transpose = 0 := by
    have ht := congrArg Matrix.transpose (commutation m n)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using ht
  rw [h, Matrix.mulVecLin_zero]

def XInsideZ (m n : ℕ) : Submodule F2 (ZOrthogonal m n) :=
  (SX m n).comap (ZOrthogonal m n).subtype

/-- The actual binary logical quotient has dimension eight for every rectangle. -/
theorem quotient_finrank (m n : ℕ) :
    Module.finrank F2 (ZOrthogonal m n ⧸ XInsideZ m n) = 8 := by
  have hx : Module.finrank F2 (SX m n) = (m + 4) * n := by
    change (HX m n).transpose.rank = _
    rw [Matrix.rank_transpose]
    exact (matrix_ranks m n).1
  have hi : Module.finrank F2 (XInsideZ m n) = (m + 4) * n :=
    (Submodule.comapSubtypeEquivOfLe (x_mem_zOrthogonal m n)).finrank_eq.trans hx
  have hz := (HZ m n).mulVecLin.finrank_range_add_finrank_ker
  have hr : Module.finrank F2 (LinearMap.range (HZ m n).mulVecLin) =
      m * (n + 4) := (matrix_ranks m n).2
  have hv : Module.finrank F2 (V m n) = 2 * ((m + 2) * (n + 2)) := by
    simp [V, Q, Cell, Module.finrank_pi_fintype]
  change Module.finrank F2 (LinearMap.range (HZ m n).mulVecLin) +
    Module.finrank F2 (ZOrthogonal m n) = Module.finrank F2 (V m n) at hz
  rw [hr, hv] at hz
  have hq := (XInsideZ m n).finrank_quotient_add_finrank
  rw [hi] at hq
  nlinarith

/-- Commutation, both ranks, and quotient dimension in one family theorem. -/
theorem parameters (m n : ℕ) :
    HX m n * (HZ m n).transpose = 0 ∧
    (HX m n).rank = (m + 4) * n ∧
    (HZ m n).rank = m * (n + 4) ∧
    Module.finrank F2 (ZOrthogonal m n ⧸ XInsideZ m n) = 8 :=
  ⟨commutation m n, (matrix_ranks m n).1, (matrix_ranks m n).2,
    quotient_finrank m n⟩

open Input

def boolIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

def qubits (m n : ℕ) : Q m n ≃ Fin (2 * ((m + 2) * (n + 2))) :=
  (Equiv.prodCongr boolIndex
    (finProdFinEquiv : Cell m n ≃ Fin ((m + 2) * (n + 2)))).trans finProdFinEquiv

def xRows (m n : ℕ) : XAnchor m n ≃ Fin ((m + 4) * n) := finProdFinEquiv

def zRows (m n : ℕ) : ZAnchor m n ≃ Fin (m * (n + 4)) := finProdFinEquiv

/-- The family as QECLean-backed CSS codes, in canonical finite-index coordinates. -/
def code (m n : ℕ) : CSSCode (2 * ((m + 2) * (n + 2))) ((m + 4) * n) (m * (n + 4)) where
  HX i q := HX m n ((xRows m n).symm i) ((qubits m n).symm q)
  HZ i q := HZ m n ((zRows m n).symm i) ((qubits m n).symm q)
  comm := by
    change ((HX m n).submatrix (xRows m n).symm (qubits m n).symm) *
      ((HZ m n).transpose.submatrix (qubits m n).symm (zRows m n).symm) = 0
    rw [Matrix.submatrix_mul_equiv, commutation]
    rfl

theorem rankX (m n : ℕ) :
    Module.finrank F2 (code m n).xStab = (m + 4) * n := by
  change Module.finrank F2 (Submodule.span F2 (Set.range (code m n).HX)) = _
  have hr : (code m n).HX.rank =
      Module.finrank F2 (Submodule.span F2 (Set.range (code m n).HX)) :=
    Matrix.rank_eq_finrank_span_row (code m n).HX
  rw [← hr]
  change ((HX m n).submatrix (xRows m n).symm (qubits m n).symm).rank = _
  rw [Matrix.rank_submatrix]
  exact (matrix_ranks m n).1

theorem rankZ (m n : ℕ) :
    Module.finrank F2 (code m n).zStab = m * (n + 4) := by
  change Module.finrank F2 (Submodule.span F2 (Set.range (code m n).HZ)) = _
  have hr : (code m n).HZ.rank =
      Module.finrank F2 (Submodule.span F2 (Set.range (code m n).HZ)) :=
    Matrix.rank_eq_finrank_span_row (code m n).HZ
  rw [← hr]
  change ((HZ m n).submatrix (zRows m n).symm (qubits m n).symm).rank = _
  rw [Matrix.rank_submatrix]
  exact (matrix_ranks m n).2

theorem encoded_qubits (m n : ℕ) :
    2 * ((m + 2) * (n + 2)) - Module.finrank F2 (code m n).xStab -
      Module.finrank F2 (code m n).zStab = 8 := by
  rw [rankX, rankZ]
  have h : 2 * ((m + 2) * (n + 2)) = (m + 4) * n + m * (n + 4) + 8 := by ring
  omega

/-- QECLean-facing parameter statement for the whole family. -/
theorem code_parameters (m n : ℕ) :
    Module.finrank F2 (code m n).xStab = (m + 4) * n ∧
    Module.finrank F2 (code m n).zStab = m * (n + 4) ∧
    2 * ((m + 2) * (n + 2)) - Module.finrank F2 (code m n).xStab -
      Module.finrank F2 (code m n).zStab = 8 :=
  ⟨rankX m n, rankZ m n, encoded_qubits m n⟩

end QldpcVerification.Planar.RectangleFamily
