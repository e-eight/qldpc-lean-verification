import QldpcVerification.Coverage
import QldpcVerification.Transport

/-! Independent components preserve logical coverage, ranks, and weight bounds. -/

namespace QldpcVerification.Components

open Matrix Module

variable {I E R : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

def slice (i : I) (x : I × E → ZMod 2) : E → ZMod 2 := fun e => x (i, e)

def extend (i : I) (x : E → ZMod 2) : I × E → ZMod 2 :=
  fun q => if q.1 = i then x q.2 else 0

def product (S : Submodule (ZMod 2) (E → ZMod 2)) :
    Submodule (ZMod 2) (I × E → ZMod 2) where
  carrier := {x | ∀ i, slice i x ∈ S}
  zero_mem' := fun _ => S.zero_mem
  add_mem' hx hy := fun i => S.add_mem (hx i) (hy i)
  smul_mem' a _ hx := fun i => S.smul_mem a (hx i)

def productEquiv (S : Submodule (ZMod 2) (E → ZMod 2)) :
    product (I := I) S ≃ₗ[ZMod 2] (I → S) where
  toFun x i := ⟨slice i x, x.property i⟩
  invFun x := ⟨fun q => (x q.1 : E → ZMod 2) q.2, fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] [DecidableEq E] in
theorem product_finrank (S : Submodule (ZMod 2) (E → ZMod 2)) :
    finrank (ZMod 2) (product (I := I) S) = Fintype.card I * finrank (ZMod 2) S := by
  rw [(productEquiv (I := I) S).finrank_eq, Module.finrank_pi_fintype]
  simp

omit [DecidableEq E] in
theorem extend_dot (i : I) (x : E → ZMod 2) (y : I × E → ZMod 2) :
    extend i x ⬝ᵥ y = x ⬝ᵥ slice i y := by
  simp [dotProduct, Fintype.sum_prod_type, extend, slice]

omit [DecidableEq E] in
theorem dot_extend (i : I) (x : I × E → ZMod 2) (y : E → ZMod 2) :
    x ⬝ᵥ extend i y = slice i x ⬝ᵥ y := by
  rw [dotProduct_comm, extend_dot, dotProduct_comm]

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem slice_extend (i j : I) (x : E → ZMod 2) :
    slice i (extend j x) = if i = j then x else 0 := by
  funext e
  by_cases h : i = j <;> simp [slice, extend, h]

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem extend_mem {S : Submodule (ZMod 2) (E → ZMod 2)} (i : I)
    {x : E → ZMod 2} (hx : x ∈ S) : extend i x ∈ product S := by
  intro j
  rw [slice_extend]
  split <;> first | exact hx | exact S.zero_mem

theorem extend_weight (i : I) (x : E → ZMod 2) : hammingNorm (extend i x) = hammingNorm x := by
  classical
  have he : Finset.univ.filter (fun q : I × E => extend i x q ≠ 0) =
      (Finset.univ.filter (fun e : E => x e ≠ 0)).image (fun e => (i, e)) := by
    ext ⟨j, e⟩
    by_cases h : j = i
    · subst j; simp [extend]
    · simp [extend, h, Ne.symm h]
  change (Finset.univ.filter (fun q : I × E => extend i x q ≠ 0)).card = _
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
  rfl

theorem slice_weight_le (i : I) (x : I × E → ZMod 2) : hammingNorm (slice i x) ≤ hammingNorm x := by
  classical
  let S := Finset.univ.filter (fun e : E => slice i x e ≠ 0)
  let T := Finset.univ.filter (fun q : I × E => x q ≠ 0)
  have hinj : Function.Injective (fun e : E => (i, e)) := fun _ _ h => (Prod.mk.inj h).2
  have hs : S.image (fun e => (i, e)) ⊆ T := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    simpa [S, T, slice] using he
  calc
    hammingNorm (slice i x) = S.card := rfl
    _ = (S.image (fun e => (i, e))).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ T.card := Finset.card_le_card hs
    _ = hammingNorm x := rfl

def block (M : Matrix R E (ZMod 2)) : Matrix (I × R) (I × E) (ZMod 2) :=
  fun r q => if r.1 = q.1 then M r.2 q.2 else 0

omit [DecidableEq E] in
theorem block_mulVec (M : Matrix R E (ZMod 2)) (x : I × E → ZMod 2) (i : I) (r : R) :
    (block M).mulVec x (i, r) = M.mulVec (slice i x) r := by
  simp [block, mulVec, dotProduct, Fintype.sum_prod_type, slice]

omit [Fintype I] [Fintype E] [DecidableEq E] in
theorem block_transpose (M : Matrix R E (ZMod 2)) : (block (I := I) M).transpose = block M.transpose := by
  ext ⟨i, e⟩ ⟨j, r⟩
  simp [block, Matrix.transpose_apply, eq_comm]

omit [Fintype E] [DecidableEq E] in
theorem rowspace_block [Fintype R] (M : Matrix R E (ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (block (I := I) M)) =
      product (Submodule.span (ZMod 2) (Set.range M)) := by
  classical
  have hr (N : Matrix R E (ZMod 2)) :
      Submodule.span (ZMod 2) (Set.range N) = LinearMap.range N.transpose.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    rfl
  have hb : Submodule.span (ZMod 2) (Set.range (block (I := I) M)) =
      LinearMap.range (block M.transpose).mulVecLin := by
    rw [← block_transpose, Matrix.range_mulVecLin]
    rfl
  ext x
  rw [hb]
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [hr]
    refine ⟨slice i y, ?_⟩
    funext e
    exact (block_mulVec M.transpose y i e).symm
  · intro hx
    have he : ∀ i, ∃ y, M.transpose.mulVec y = slice i x := by
      intro i
      have hi := hx i
      rw [hr] at hi
      exact hi
    choose y hy using he
    refine ⟨fun q => y q.1 q.2, ?_⟩
    funext ⟨i, e⟩
    change (block M.transpose).mulVec (fun q => y q.1 q.2) (i, e) = x (i, e)
    rw [block_mulVec]
    exact congrFun (hy i) e

omit [DecidableEq E] in
theorem kernel_block [Fintype R] (M : Matrix R E (ZMod 2)) :
    LinearMap.ker (block (I := I) M).mulVecLin = product (LinearMap.ker M.mulVecLin) := by
  ext x
  constructor
  · intro hx i
    funext r
    exact (block_mulVec M x i r).symm.trans (congrFun hx (i, r))
  · intro hx
    funext ⟨i, r⟩
    change (block M).mulVec x (i, r) = 0
    rw [block_mulVec]
    exact congrFun (hx i) r

noncomputable def coverage {S B : Submodule (ZMod 2) (E → ZMod 2)} {k c : ℕ}
    (C : CoverageCertificate S B k) :
    CoverageCertificate (product (I := Fin c) S) (product B) (c * k) where
  boundary_le x hx i := C.boundary_le (hx i)
  detectors j := extend (finProdFinEquiv.symm j).1 (C.detectors (finProdFinEquiv.symm j).2)
  witnesses j := extend (finProdFinEquiv.symm j).1 (C.witnesses (finProdFinEquiv.symm j).2)
  witness_mem j := extend_mem _ (C.witness_mem _)
  boundary_zero x hx j := by
    rw [dot_extend]
    exact C.boundary_zero _ (hx _) _
  paired i j := by
    rw [extend_dot, slice_extend]
    by_cases h : i = j
    · subst j
      simpa using C.paired (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).2
    · have hij : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j :=
        fun he => h (finProdFinEquiv.symm.injective he)
      rw [if_neg h]
      by_cases hf : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
      · have hs : (finProdFinEquiv.symm i).2 ≠ (finProdFinEquiv.symm j).2 :=
          fun he => hij (Prod.ext hf he)
        rw [if_pos hf, C.paired, if_neg hs]
      · rw [if_neg hf, dotProduct_zero]
  dimension_bound := by
    rw [product_finrank, product_finrank, Fintype.card_fin]
    have h := Nat.mul_le_mul_left c C.dimension_bound
    simpa [Nat.mul_add] using h

theorem lower {S B : Submodule (ZMod 2) (E → ZMod 2)} (D : ℕ)
    (hbound : ∀ x, x ∈ S → x ∉ B → D ≤ hammingNorm x)
    (x : I × E → ZMod 2) (hx : x ∈ product S) (hb : x ∉ product B) : D ≤ hammingNorm x := by
  have hn : ∃ i, slice i x ∉ B := by simpa [product] using hb
  obtain ⟨i, hi⟩ := hn
  exact (hbound _ (hx i) hi).trans (slice_weight_le i x)

theorem extend_nonboundary {S B : Submodule (ZMod 2) (E → ZMod 2)} (i : I)
    (x : E → ZMod 2) (hx : x ∈ S) (hb : x ∉ B) :
    extend i x ∈ product S ∧ extend i x ∉ product B := by
  refine ⟨extend_mem i hx, ?_⟩
  intro h
  have hi := h i
  rw [slice_extend, if_pos rfl] at hi
  exact hb hi

end QldpcVerification.Components
