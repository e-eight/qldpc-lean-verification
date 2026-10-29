import QldpcCert.Spec
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# Certificate lemmas

Proved once, for every code. Instance files only supply data and let Lean
check the finite facts.

* `dotProduct_eq_zero_of_mem_span`: a vector in the kernel of `H` is orthogonal
  to the row space of `H`.
* `card_le_mul_hammingNorm`: the double-counting bound behind packing
  certificates.
* `le_finrank_span_rows`: a rank lower bound from a pivot certificate.
* `finrank_ker_add_finrank_span_rows`: rank–nullity in row-space form.
* `distX_ge_of_packing`: the packing certificate for codes with one logical
  qubit (`k = 1`).
-/

open Matrix Finset Module

namespace CSSCode

variable {n : ℕ}

/-- A vector in the kernel of `H` is orthogonal to every vector in the row space
of `H`. -/
theorem dotProduct_eq_zero_of_mem_span {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    {x : Vec n} (hx : H.mulVec x = 0) {s : Vec n}
    (hs : s ∈ Submodule.span (ZMod 2) (Set.range H)) : s ⬝ᵥ x = 0 := by
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact congrFun hx i
  | zero => exact zero_dotProduct x
  | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]

/-- Double counting. If `x` pairs to `1` with each `z i`, and no qubit lies in
the support of more than `c` of the `z i`, then there are at most
`c * hammingNorm x` of them. -/
theorem card_le_mul_hammingNorm {ι : Type*} [Fintype ι] (x : Vec n) (z : ι → Vec n)
    (c : ℕ) (hpair : ∀ i, x ⬝ᵥ z i = 1)
    (hcov : ∀ q, (univ.filter fun i => z i q ≠ 0).card ≤ c) :
    Fintype.card ι ≤ c * hammingNorm x := by
  classical
  -- Each `z i` meets the support of `x`: otherwise the dot product would be `0`.
  have hmeet : ∀ i, 1 ≤ (univ.filter fun q => x q ≠ 0 ∧ z i q ≠ 0).card := by
    intro i
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro h
    have hzero : x ⬝ᵥ z i = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      by_cases hxq : x q = 0
      · simp [hxq]
      · have hzq : z i q = 0 := by
          by_contra hzq
          exact h (Finset.mem_univ q) ⟨hxq, hzq⟩
        simp [hzq]
    rw [hpair i] at hzero
    exact one_ne_zero hzero
  calc Fintype.card ι
      = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, (univ.filter fun q => x q ≠ 0 ∧ z i q ≠ 0).card :=
        Finset.sum_le_sum fun i _ => hmeet i
    _ = ∑ i, ∑ q, if x q ≠ 0 ∧ z i q ≠ 0 then 1 else 0 := by
        simp only [Finset.card_filter]
    _ = ∑ q, ∑ i, if x q ≠ 0 ∧ z i q ≠ 0 then 1 else 0 := Finset.sum_comm
    _ = ∑ q ∈ univ.filter (fun q => x q ≠ 0), (univ.filter fun i => z i q ≠ 0).card := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases hxq : x q ≠ 0
        · simp [hxq, Finset.card_filter]
        · simp [hxq]
    _ ≤ ∑ _q ∈ univ.filter (fun q => x q ≠ 0), c :=
        Finset.sum_le_sum fun q _ => hcov q
    _ = c * hammingNorm x := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        rfl

/-- Rank lower bound from a pivot certificate: if `(T * H) i (p j) = [i = j]`,
the rows of `T * H` are `r` independent vectors in the row space of `H`. -/
theorem le_finrank_span_rows {m r : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (T : Matrix (Fin r) (Fin m) (ZMod 2)) (p : Fin r → Fin n)
    (hp : ∀ i j, (T * H) i (p j) = if i = j then 1 else 0) :
    r ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) := by
  set S := Submodule.span (ZMod 2) (Set.range H)
  have hmem : ∀ i, (T * H) i ∈ S := by
    intro i
    have h : (T * H) i = ∑ k, T i k • H k := by
      ext j
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [h]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let v : Fin r → S := fun i => ⟨(T * H) i, hmem i⟩
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h := congrArg (fun s : S => (s : Vec n) (p j)) hg
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, v, hp, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
    exact h
  simpa using hli.fintype_card_le_finrank

/-- Rank–nullity in row-space form: `dim ker H + dim rowspace H = n`. -/
theorem finrank_ker_add_finrank_span_rows {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) :
    finrank (ZMod 2) (LinearMap.ker H.mulVecLin) +
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) = n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  rw [Module.finrank_fin_fun] at h1
  have h2 : H.rank = finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) :=
    Matrix.rank_eq_finrank_span_row H
  have h3 : H.rank = finrank (ZMod 2) (LinearMap.range H.mulVecLin) := by rw [Matrix.rank]
  omega

/-- An element of `𝔽₂` is `0` or `1`. -/
theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_ker_iff {m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Vec n) :
    v ∈ LinearMap.ker H.mulVecLin ↔ H.mulVec v = 0 := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]

variable {mX mZ : ℕ} (C : CSSCode n mX mZ)

/-- Every row of `HX` commutes with the Z checks. -/
theorem mulVec_HX_row (i : Fin mX) : C.HZ.mulVec (C.HX i) = 0 := by
  funext j
  have h := congrFun (congrFun C.comm i) j
  rw [Matrix.mul_apply'] at h
  simp only [Matrix.transpose_apply, Matrix.zero_apply] at h
  simp only [Matrix.mulVec, Pi.zero_apply]
  rw [dotProduct_comm]
  exact h

theorem xStab_le_ker : C.xStab ≤ LinearMap.ker C.HZ.mulVecLin := by
  rw [xStab, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, mem_ker_iff]
  exact C.mulVec_HX_row i

/-- **Packing certificate, one logical qubit.** Suppose `w` is an X-type logical
and the `z i` are Z-type logicals that each pair to `1` with `w`, with no qubit in
more than `c` of them. If the stabilizer ranks leave room for only one logical
qubit, then every nontrivial X-type logical `x` satisfies
`card ι ≤ c * hammingNorm x`. -/
theorem distX_ge_of_packing (w : Vec n) (hw : C.HZ.mulVec w = 0)
    {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → Vec n) (hz : ∀ i, C.HX.mulVec (z i) = 0)
    (hwz : ∀ i, w ⬝ᵥ z i = 1) (c : ℕ)
    (hcov : ∀ q, (univ.filter fun i => z i q ≠ 0).card ≤ c)
    (hdim : n ≤ finrank (ZMod 2) C.xStab + finrank (ZMod 2) C.zStab + 1)
    (x : Vec n) (hx : C.IsXLogical x) : Fintype.card ι ≤ c * hammingNorm x := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- `w` is not a stabilizer: it pairs to `1` with a Z-type logical.
  have hw_not : w ∉ C.xStab := by
    intro hmem
    have h := dotProduct_eq_zero_of_mem_span C.HX (hz i₀) hmem
    rw [hwz i₀] at h
    exact one_ne_zero h
  -- So `xStab ⊔ span {w}` has dimension `dim xStab + 1`, which is all of `ker HZ`.
  set W := Submodule.span (ZMod 2) ({w} : Set (Vec n))
  have hle : C.xStab ⊔ W ≤ LinearMap.ker C.HZ.mulVecLin := by
    refine sup_le C.xStab_le_ker ?_
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_ker_iff]
    exact hw
  have hinf : C.xStab ⊓ W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy2
    rcases zmod2_cases a with rfl | rfl
    · exact zero_smul _ _
    · rw [one_smul] at hy1
      exact absurd hy1 hw_not
  have hW : finrank (ZMod 2) W = 1 :=
    finrank_span_singleton (fun h => hw_not (h ▸ Submodule.zero_mem _))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq C.xStab W
  rw [hinf, finrank_bot, hW, add_zero] at hsup
  have hker := finrank_ker_add_finrank_span_rows C.HZ
  have hfin : finrank (ZMod 2) (LinearMap.ker C.HZ.mulVecLin) ≤
      finrank (ZMod 2) ↥(C.xStab ⊔ W) := by
    rw [hsup]
    have : finrank (ZMod 2) C.zStab = finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range C.HZ)) := rfl
    omega
  have heq := Submodule.eq_of_le_of_finrank_le hle hfin
  -- Write `x = s + a • w` with `s` a stabilizer; `a = 1` because `x` is nontrivial.
  have hxker : x ∈ LinearMap.ker C.HZ.mulVecLin := (mem_ker_iff _ _).mpr hx.1
  rw [← heq] at hxker
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hxker
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rcases zmod2_cases a with rfl | rfl
  · rw [zero_smul, add_zero] at hx
    exact absurd hs hx.2
  · refine card_le_mul_hammingNorm _ z c (fun i => ?_) hcov
    rw [add_dotProduct, dotProduct_eq_zero_of_mem_span C.HX (hz i) hs, one_smul, zero_add]
    exact hwz i

/-- The same code with the roles of X and Z exchanged. -/
def swap : CSSCode n mZ mX where
  HX := C.HZ
  HZ := C.HX
  comm := by
    rw [← Matrix.transpose_transpose C.HZ, ← Matrix.transpose_mul, C.comm, Matrix.transpose_zero]

theorem distZ_iff_swap (d : ℕ) : C.DistZ d ↔ C.swap.DistX d := Iff.rfl

end CSSCode
