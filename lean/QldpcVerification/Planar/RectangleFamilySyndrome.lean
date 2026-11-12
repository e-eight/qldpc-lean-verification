import QldpcVerification.Planar.RectangleFamily
import QldpcVerification.Planar.BulkExactness
import Mathlib.InformationTheory.Hamming

/-! Polynomial encoding and full syndrome on arbitrary rectangles. -/
namespace QldpcVerification.Planar.RectangleFamilySyndrome

open Polynomial RectangleFamily

noncomputable section

abbrev Bivariate := BulkExactness.Bivariate
abbrev Grid (M N : ℕ) := Fin M → Fin N → F2

/-- The two independent support bounds of an ordinary bivariate polynomial. -/
def InRectangle (d e : ℕ) (p : Bivariate) : Prop :=
  p.natDegree ≤ d ∧ (BulkExactness.swap p).natDegree ≤ e

def gridEncode (M N : ℕ) : Grid M N →ₗ[F2] Bivariate where
  toFun c := ∑ i : Fin M, monomial i.val (BoundaryRecurrence.pack M N c i)
  map_add' c d := by simp [map_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [map_smul, Pi.smul_apply, Finset.smul_sum, Polynomial.smul_monomial,
      RingHom.id_apply]

@[simp] theorem gridEncode_outer_coeff {M N : ℕ} (c : Grid M N) (i : Fin M) :
    (gridEncode M N c).coeff i.val = BoundaryRecurrence.pack M N c i := by
  classical
  change (∑ k : Fin M, monomial k.val (BoundaryRecurrence.pack M N c k)).coeff i.val = _
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [show k.val ≠ i.val from fun h => hki (Fin.ext h)]
  · simp

@[simp] theorem gridEncode_coeff {M N : ℕ} (c : Grid M N) (i : Fin M) (j : Fin N) :
    ((gridEncode M N c).coeff i.val).coeff j.val = c i j := by
  rw [gridEncode_outer_coeff]
  exact BoundaryRecurrence.pack_coeff c i j

theorem gridEncode_outer_zero {M N : ℕ} (c : Grid M N) (i : ℕ) (hi : M ≤ i) :
    (gridEncode M N c).coeff i = 0 := by
  classical
  change (∑ k : Fin M, monomial k.val (BoundaryRecurrence.pack M N c k)).coeff i = 0
  simp only [finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg (by have := k.isLt; omega)]

theorem gridEncode_coeff_zero {M N : ℕ} (c : Grid M N) (i j : ℕ)
    (hout : M ≤ i ∨ N ≤ j) : ((gridEncode M N c).coeff i).coeff j = 0 := by
  rcases hout with hi | hj
  · rw [gridEncode_outer_zero c i hi]
    simp
  · by_cases hi : i < M
    · rw [gridEncode_outer_coeff c ⟨i, hi⟩]
      exact BoundaryRecurrence.pack_supportedBelow c ⟨i, hi⟩ j hj
    · rw [gridEncode_outer_zero c i (by omega)]
      simp

theorem inRectangle_coeff_zero {d e : ℕ} {p : Bivariate} (hp : InRectangle d e p)
    (i j : ℕ) (hout : d < i ∨ e < j) : (p.coeff i).coeff j = 0 := by
  rcases hout with hi | hj
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp.1 hi)]
    simp
  · rw [← BulkExactness.swap_coeff]
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp.2 hj)]
    simp

theorem gridEncode_inRectangle (d e : ℕ) (c : Grid (d + 1) (e + 1)) :
    InRectangle d e (gridEncode (d + 1) (e + 1) c) := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact gridEncode_outer_zero c i (by omega)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Polynomial.ext
    intro j
    rw [BulkExactness.swap_coeff]
    simpa using gridEncode_coeff_zero c j i (Or.inr (by omega))

variable {m n : ℕ}

def blockEncode (m n : ℕ) (b : Bool) : V m n →ₗ[F2] Bivariate where
  toFun w := gridEncode (m + 2) (n + 2) (fun i j => w (b, (i, j)))
  map_add' w z := map_add (gridEncode (m + 2) (n + 2)) _ _
  map_smul' r w := map_smul (gridEncode (m + 2) (n + 2)) r _

def encode (m n : ℕ) : V m n →ₗ[F2] (Bivariate × Bivariate) :=
  (blockEncode m n false).prod (blockEncode m n true)

@[simp] theorem blockEncode_coeff (w : V m n) (b : Bool)
    (i : Fin (m + 2)) (j : Fin (n + 2)) :
    ((blockEncode m n b w).coeff i.val).coeff j.val = w (b, (i, j)) :=
  gridEncode_coeff _ i j

theorem encode_injective (m n : ℕ) : Function.Injective (encode m n) := by
  intro w z h
  funext q
  rcases q with ⟨b, i, j⟩
  cases b
  · have he := congrArg (fun p : Bivariate × Bivariate => (p.1.coeff i.val).coeff j.val) h
    simpa [encode] using he
  · have he := congrArg (fun p : Bivariate × Bivariate => (p.2.coeff i.val).coeff j.val) h
    simpa [encode] using he

theorem encode_inRectangle (w : V m n) :
    InRectangle (m + 1) (n + 1) (encode m n w).1 ∧
      InRectangle (m + 1) (n + 1) (encode m n w).2 :=
  ⟨gridEncode_inRectangle (m + 1) (n + 1) _,
    gridEncode_inRectangle (m + 1) (n + 1) _⟩

def polynomialSyndrome : (Bivariate × Bivariate) →ₗ[F2] Bivariate where
  toFun p := BulkExactness.g * p.1 + BulkExactness.f * p.2
  map_add' p q := by simp [mul_add, add_assoc, add_left_comm, add_comm]
  map_smul' r p := by simp [mul_smul_comm, smul_add]

def fullSyndrome (m n : ℕ) : V m n →ₗ[F2] Bivariate :=
  polynomialSyndrome.comp (encode m n)

theorem fullSyndrome_apply (w : V m n) :
    fullSyndrome m n w = BulkExactness.g * (encode m n w).1 +
      BulkExactness.f * (encode m n w).2 := rfl

theorem inRectangle_mul {d e D E : ℕ} {p q : Bivariate}
    (hp : InRectangle d e p) (hq : InRectangle D E q) :
    InRectangle (d + D) (e + E) (p * q) := by
  constructor
  · exact natDegree_mul_le.trans (Nat.add_le_add hp.1 hq.1)
  · rw [map_mul]
    exact natDegree_mul_le.trans (Nat.add_le_add hp.2 hq.2)

theorem inRectangle_add {d e : ℕ} {p q : Bivariate}
    (hp : InRectangle d e p) (hq : InRectangle d e q) :
    InRectangle d e (p + q) := by
  constructor
  · exact natDegree_add_le_of_degree_le hp.1 hq.1
  · rw [map_add]
    exact natDegree_add_le_of_degree_le hp.2 hq.2

theorem f_inRectangle : InRectangle 2 2 BulkExactness.f :=
  ⟨le_of_eq BulkExactness.f_natDegree, le_of_eq BulkExactness.swap_f_natDegree⟩

theorem g_inRectangle : InRectangle 2 2 BulkExactness.g := by
  constructor
  · change (C BulkExactness.t * (X : Bivariate) ^ 2 + 1).natDegree ≤ 2
    exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le _ 2) (by simp)
  · have he : BulkExactness.swap BulkExactness.g =
        C (BulkExactness.Y ^ 2) * (X : Bivariate) ^ 2 +
          C (BulkExactness.Y ^ 2) * X + 1 := by
      simp only [BulkExactness.swap, BulkExactness.g, BulkExactness.companion,
        BulkExactness.t, BulkExactness.Y, map_add, map_mul, map_pow, map_one,
        Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y]
      ring
    rw [he]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_C_mul_X_pow_le _ 2
      · exact natDegree_mul_le.trans (by simp)
    · simp

theorem fullSyndrome_inRectangle (w : V m n) :
    InRectangle (m + 3) (n + 3) (fullSyndrome m n w) := by
  rw [fullSyndrome_apply]
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    inRectangle_add
      (inRectangle_mul g_inRectangle (encode_inRectangle w).1)
      (inRectangle_mul f_inRectangle (encode_inRectangle w).2)

theorem fullSyndrome_coeff_zero (w : V m n) (i j : ℕ)
    (hout : m + 4 ≤ i ∨ n + 4 ≤ j) :
    ((fullSyndrome m n w).coeff i).coeff j = 0 :=
  inRectangle_coeff_zero (fullSyndrome_inRectangle w) i j (by omega)

end
end QldpcVerification.Planar.RectangleFamilySyndrome
