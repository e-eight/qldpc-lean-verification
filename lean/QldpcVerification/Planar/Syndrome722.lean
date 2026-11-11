import QldpcVerification.Planar.Commutation
import QldpcVerification.Planar.BoundaryRecurrence
import QldpcVerification.Planar.BulkExactness
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Prod

/-!
# Finite physical coordinates and the full polynomial syndrome

physicalV uses exactly Commutation.Q: false is A, true is B, and the
two finite indices are row X then column Y. The outer polynomial variable
is X. No periodic quotient or boundary syndrome truncation occurs here.

The finite 17-by-17 multiplier map is proved injective and its range is
identified with the full-syndrome kernel. The dimension 289 is a conclusion,
not a hypothesis. Polynomial support bounds prove that coefficient decoding
does not discard either component of a bulk multiple.

PROPOSITION: independent review and capped Lean replay of this adapter pending.
No Lean process was run by the author. The guarded audit is a replay target,
not a claim that this source has already passed the kernel.
-/

namespace QldpcVerification.Planar.Syndrome722

open Polynomial

noncomputable section

abbrev F2 := Commutation.F2
abbrev Bivariate := BulkExactness.Bivariate
abbrev Grid (N : ℕ) := Fin N → Fin N → F2
abbrev physicalV := Commutation.Q → F2

set_option maxRecDepth 2000 in
/-- Pack columns using the existing recurrence pack, then pack rows as outer X. -/
def squareEncode (N : ℕ) : Grid N →ₗ[F2] Bivariate where
  toFun c := ∑ i : Fin N, monomial i.val (BoundaryRecurrence.pack N N c i)
  map_add' c d := by
    simp [map_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp only [map_smul, Pi.smul_apply, Finset.smul_sum, Polynomial.smul_monomial,
      RingHom.id_apply]

/-- Read coefficients at the finite square; this map alone is a truncation. -/
def squareDecode (N : ℕ) : Bivariate →ₗ[F2] Grid N where
  toFun p i j := (p.coeff i.val).coeff j.val
  map_add' p q := by
    funext i j
    simp
  map_smul' r p := by
    funext i j
    simp

@[simp] theorem squareEncode_outer_coeff {N : ℕ} (c : Grid N) (i : Fin N) :
    (squareEncode N c).coeff i.val = BoundaryRecurrence.pack N N c i := by
  classical
  change (∑ k : Fin N, monomial k.val (BoundaryRecurrence.pack N N c k)).coeff
    i.val = _
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [show k.val ≠ i.val from fun h => hki (Fin.ext h)]
  · simp

@[simp] theorem squareEncode_coeff {N : ℕ} (c : Grid N) (i j : Fin N) :
    ((squareEncode N c).coeff i.val).coeff j.val = c i j := by
  rw [squareEncode_outer_coeff]
  exact BoundaryRecurrence.pack_coeff c i j

theorem squareEncode_outer_zero {N : ℕ} (c : Grid N) (i : ℕ) (hi : N ≤ i) :
    (squareEncode N c).coeff i = 0 := by
  classical
  change (∑ k : Fin N, monomial k.val (BoundaryRecurrence.pack N N c k)).coeff
    i = 0
  simp only [finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro k _
  rw [if_neg (by have := k.isLt; omega)]

/-- Coefficient support is proved for all natural indices, including outside the board. -/
theorem squareEncode_coeff_zero {N : ℕ} (c : Grid N) (i j : ℕ)
    (hout : N ≤ i ∨ N ≤ j) : ((squareEncode N c).coeff i).coeff j = 0 := by
  rcases hout with hi | hj
  · rw [squareEncode_outer_zero c i hi]
    simp
  · by_cases hi : i < N
    · have he := squareEncode_outer_coeff c (⟨i, hi⟩ : Fin N)
      change (squareEncode N c).coeff i = _ at he
      rw [he]
      exact BoundaryRecurrence.pack_supportedBelow c ⟨i, hi⟩ j hj
    · rw [squareEncode_outer_zero c i (by omega)]
      simp

@[simp] theorem squareDecode_squareEncode (N : ℕ) (c : Grid N) :
    squareDecode N (squareEncode N c) = c := by
  funext i j
  exact squareEncode_coeff c i j

theorem squareEncode_injective (N : ℕ) : Function.Injective (squareEncode N) := by
  intro c d h
  have he := congrArg (squareDecode N) h
  simpa only [squareDecode_squareEncode] using he

/-- No coefficient is lost when the polynomial has the specified finite support. -/
theorem squareEncode_squareDecode_of_coeff {N : ℕ} (p : Bivariate)
    (hp : ∀ i j, N ≤ i ∨ N ≤ j → (p.coeff i).coeff j = 0) :
    squareEncode N (squareDecode N p) = p := by
  apply Polynomial.ext
  intro i
  apply Polynomial.ext
  intro j
  by_cases hi : i < N
  · by_cases hj : j < N
    · exact squareEncode_coeff (squareDecode N p) ⟨i, hi⟩ ⟨j, hj⟩
    · rw [squareEncode_coeff_zero _ i j (Or.inr (by omega)),
        hp i j (Or.inr (by omega))]
  · rw [squareEncode_coeff_zero _ i j (Or.inl (by omega)),
      hp i j (Or.inl (by omega))]

/-- Translate coefficient support into both degree bounds used by bulk exactness. -/
theorem inSquare_of_coeff_zero {d : ℕ} (p : Bivariate)
    (hp : ∀ i j, d < i ∨ d < j → (p.coeff i).coeff j = 0) :
    BulkExactness.InSquare d p := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Polynomial.ext
    intro j
    simpa using hp i j (Or.inl hi)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    apply Polynomial.ext
    intro j
    rw [BulkExactness.swap_coeff]
    simpa using hp j i (Or.inr hi)

theorem squareEncode_inSquare (d : ℕ) (c : Grid (d + 1)) :
    BulkExactness.InSquare d (squareEncode (d + 1) c) := by
  apply inSquare_of_coeff_zero
  intro i j hij
  exact squareEncode_coeff_zero c i j (by omega)

theorem squareEncode_squareDecode (d : ℕ) (p : Bivariate)
    (hp : BulkExactness.InSquare d p) :
    squareEncode (d + 1) (squareDecode (d + 1) p) = p := by
  apply squareEncode_squareDecode_of_coeff
  intro i j hij
  exact BulkExactness.inSquare_coeff_zero hp i j (by omega)

/-- One species in the literal physical coordinate type, with row as outer X. -/
def blockEncode (b : Bool) : physicalV →ₗ[F2] Bivariate where
  toFun w := squareEncode 19 (fun i j => w (b, (i, j)))
  map_add' w z := by
    exact map_add (squareEncode 19) _ _
  map_smul' r w := by
    exact map_smul (squareEncode 19) r _

/-- A and B polynomials, in that order. -/
def encode : physicalV →ₗ[F2] (Bivariate × Bivariate) :=
  (blockEncode false).prod (blockEncode true)

/-- Literal coefficient readout: false=A, true=B. -/
def decode : (Bivariate × Bivariate) →ₗ[F2] physicalV where
  toFun p q := if q.1 then (p.2.coeff q.2.1.val).coeff q.2.2.val
    else (p.1.coeff q.2.1.val).coeff q.2.2.val
  map_add' p r := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> simp
  map_smul' r p := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> simp

@[simp] theorem blockEncode_coeff (w : physicalV) (b : Bool) (i j : Fin 19) :
    ((blockEncode b w).coeff i.val).coeff j.val = w (b, (i, j)) :=
  squareEncode_coeff _ i j

@[simp] theorem decode_encode (w : physicalV) : decode (encode w) = w := by
  funext q
  rcases q with ⟨b, i, j⟩
  cases b <;> simp [decode, encode]

theorem encode_injective : Function.Injective encode := by
  intro w z h
  have he := congrArg decode h
  simpa only [decode_encode] using he

theorem encode_inSquare (w : physicalV) :
    BulkExactness.InSquare 18 (encode w).1 ∧
      BulkExactness.InSquare 18 (encode w).2 :=
  ⟨squareEncode_inSquare 18 _, squareEncode_inSquare 18 _⟩

/-- Decoding followed by encoding is the identity on the physical support square. -/
theorem encode_decode (p : Bivariate × Bivariate)
    (hp : BulkExactness.InSquare 18 p.1 ∧ BulkExactness.InSquare 18 p.2) :
    encode (decode p) = p := by
  apply Prod.ext
  · change squareEncode 19 (squareDecode 19 p.1) = p.1
    exact squareEncode_squareDecode 18 p.1 hp.1
  · change squareEncode 19 (squareDecode 19 p.2) = p.2
    exact squareEncode_squareDecode 18 p.2 hp.2

/-- Full polynomial syndrome, with no boundary coefficients suppressed. -/
def polynomialSyndrome : (Bivariate × Bivariate) →ₗ[F2] Bivariate where
  toFun p := BulkExactness.g * p.1 + BulkExactness.f * p.2
  map_add' p q := by
    simp [mul_add, add_assoc, add_left_comm, add_comm]
  map_smul' r p := by
    simp [mul_smul_comm, smul_add]

/-- The actual physical-to-full-syndrome linear map on Commutation.Q → F2. -/
def fullSyndrome : physicalV →ₗ[F2] Bivariate :=
  polynomialSyndrome.comp encode

theorem fullSyndrome_apply (w : physicalV) :
    fullSyndrome w = BulkExactness.g * (encode w).1 +
      BulkExactness.f * (encode w).2 := rfl

/-- Both support extents add under multiplication, including zero factors. -/
theorem inSquare_mul {d e : ℕ} {p q : Bivariate}
    (hp : BulkExactness.InSquare d p) (hq : BulkExactness.InSquare e q) :
    BulkExactness.InSquare (d + e) (p * q) := by
  constructor
  · exact natDegree_mul_le.trans (Nat.add_le_add hp.1 hq.1)
  · rw [map_mul]
    exact natDegree_mul_le.trans (Nat.add_le_add hp.2 hq.2)

theorem inSquare_add {d : ℕ} {p q : Bivariate}
    (hp : BulkExactness.InSquare d p) (hq : BulkExactness.InSquare d q) :
    BulkExactness.InSquare d (p + q) := by
  constructor
  · exact natDegree_add_le_of_degree_le hp.1 hq.1
  · rw [map_add]
    exact natDegree_add_le_of_degree_le hp.2 hq.2

theorem f_inSquare : BulkExactness.InSquare 2 BulkExactness.f :=
  ⟨le_of_eq BulkExactness.f_natDegree, le_of_eq BulkExactness.swap_f_natDegree⟩

theorem swap_g :
    BulkExactness.swap BulkExactness.g =
      C (BulkExactness.Y ^ 2) * (X : Bivariate) ^ 2 +
        C (BulkExactness.Y ^ 2) * X + 1 := by
  simp only [BulkExactness.swap, BulkExactness.g, BulkExactness.companion,
    BulkExactness.t, BulkExactness.Y, map_add, map_mul, map_pow, map_one,
    Polynomial.Bivariate.swap_X, Polynomial.Bivariate.swap_Y]
  ring

theorem g_inSquare : BulkExactness.InSquare 2 BulkExactness.g := by
  constructor
  · change (C BulkExactness.t * (X : Bivariate) ^ 2 + 1).natDegree ≤ 2
    exact natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le _ 2) (by simp)
  · rw [swap_g]
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_C_mul_X_pow_le _ 2
      · exact natDegree_mul_le.trans (by simp)
    · simp

/-- The full syndrome has only the 21-by-21 coefficient square, before cycle constraints. -/
theorem fullSyndrome_inSquare (w : physicalV) :
    BulkExactness.InSquare 20 (fullSyndrome w) := by
  rw [fullSyndrome_apply]
  exact inSquare_add
    (inSquare_mul g_inSquare (encode_inSquare w).1)
    (inSquare_mul f_inSquare (encode_inSquare w).2)

theorem fullSyndrome_coeff_zero (w : physicalV) (i j : ℕ)
    (hout : 21 ≤ i ∨ 21 ≤ j) : ((fullSyndrome w).coeff i).coeff j = 0 :=
  BulkExactness.inSquare_coeff_zero (fullSyndrome_inSquare w) i j (by omega)

/- BoundaryResidue compatibility:
X low Side = (fun j : Fin 21 => (p.coeff 0).coeff j.val,
              fun j : Fin 21 => (p.coeff 1).coeff j.val).
X high uses outer rows 19 and 20 in the same order.
Reflected-Z low Side reads (p.coeff i.val).coeff 0 and .coeff 1;
reflected-Z high reads inner columns 19 and 20.
No reflection, swap, or truncation is hidden in fullSyndrome itself.
-/

/-- The untruncated bulk generator, as a linear map over physical scalars. -/
def bulkPair : Bivariate →ₗ[F2] (Bivariate × Bivariate) where
  toFun h := (BulkExactness.f * h, BulkExactness.g * h)
  map_add' h k := by
    simp [mul_add]
  map_smul' r h := by
    simp [mul_smul_comm]

/-- A finite 17-by-17 array synthesizes a physical bulk stabilizer combination. -/
def finiteBulk : Grid 17 →ₗ[F2] physicalV :=
  decode.comp (bulkPair.comp (squareEncode 17))

theorem bulkPair_inSquare (c : Grid 17) :
    BulkExactness.InSquare 18 (bulkPair (squareEncode 17 c)).1 ∧
      BulkExactness.InSquare 18 (bulkPair (squareEncode 17 c)).2 := by
  constructor
  · exact inSquare_mul f_inSquare (squareEncode_inSquare 16 c)
  · exact inSquare_mul g_inSquare (squareEncode_inSquare 16 c)

/-- This identity explicitly proves that finite physical readout loses no bulk coefficient. -/
@[simp] theorem encode_finiteBulk (c : Grid 17) :
    encode (finiteBulk c) =
      (BulkExactness.f * squareEncode 17 c, BulkExactness.g * squareEncode 17 c) := by
  change encode (decode (bulkPair (squareEncode 17 c))) =
    bulkPair (squareEncode 17 c)
  exact encode_decode _ (bulkPair_inSquare c)

theorem finiteBulk_injective : Function.Injective finiteBulk := by
  intro c d h
  have he := congrArg (fun w : physicalV => (encode w).1) h
  have hm : BulkExactness.f * squareEncode 17 c =
      BulkExactness.f * squareEncode 17 d := by
    simpa only [encode_finiteBulk] using he
  exact squareEncode_injective 17 (mul_left_cancel₀ BulkExactness.f_ne_zero hm)

/-- Kernel recognition in the physical space, without any rank or matrix hypothesis. -/
theorem finiteBulk_range_eq_kernel :
    LinearMap.range finiteBulk = LinearMap.ker fullSyndrome := by
  apply Submodule.ext
  intro w
  constructor
  · rintro ⟨c, rfl⟩
    change polynomialSyndrome (encode (finiteBulk c)) = 0
    rw [encode_finiteBulk]
    exact BulkExactness.bulk_cycle (squareEncode 17 c)
  · intro hw
    have hcycle : BulkExactness.g * (encode w).1 +
        BulkExactness.f * (encode w).2 = 0 := hw
    obtain ⟨h, hu, hv, hs⟩ := BulkExactness.bulk_exactness_square
      (encode w).1 (encode w).2 hcycle (encode_inSquare w).1
    let c : Grid 17 := squareDecode 17 h
    have hc : squareEncode 17 c = h := squareEncode_squareDecode 16 h hs
    refine ⟨c, ?_⟩
    apply encode_injective
    rw [encode_finiteBulk, hc]
    exact Prod.ext hu.symm hv.symm

/-- Concrete finite bridge: the full-syndrome kernel on 722 coordinates has dimension 289. -/
theorem fullSyndrome_kernel_finrank :
    Module.finrank F2 (LinearMap.ker fullSyndrome) = 289 := by
  rw [← finiteBulk_range_eq_kernel]
  rw [LinearMap.finrank_range_of_inj finiteBulk_injective]
  simp [Grid, Module.finrank_pi_fintype, Module.finrank_pi]

/-- The underlying physical space really has 722 binary coordinates. -/
theorem physicalV_finrank : Module.finrank F2 physicalV = 722 := by
  simp [physicalV, Commutation.Q, Commutation.Cell, Module.finrank_pi]

end

end QldpcVerification.Planar.Syndrome722
