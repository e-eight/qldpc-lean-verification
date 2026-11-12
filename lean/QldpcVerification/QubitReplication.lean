import QldpcVerification.ComponentDistance
import QldpcVerification.QubitRemoval

/-!
Exact CSS distances under repetition of every physical coordinate. The X
checks are anchored old checks and weight-two checks equating replicas; the
Z checks replicate each old row. All statements allow dependent check rows.
-/

namespace QldpcVerification.QubitReplication

open Matrix Module

variable {I E RX RZ : Type} [Fintype I] [DecidableEq I]
  [Fintype E] [DecidableEq E]

/-- Sum the physical bits in each replica fiber. -/
def parity : (I × E → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun x q := ∑ i, x (i, q)
  map_add' x y := by ext q; simp [Finset.sum_add_distrib]
  map_smul' a x := by ext q; simp [Finset.mul_sum]

/-- Repeat a bit on every physical replica. -/
def replicate : (E → ZMod 2) →ₗ[ZMod 2] (I × E → ZMod 2) where
  toFun z q := z q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A weight-preserving section of the parity map. -/
def embed (i₀ : I) : (E → ZMod 2) →ₗ[ZMod 2] (I × E → ZMod 2) where
  toFun := Components.extend i₀
  map_add' x y := by ext ⟨i, q⟩; by_cases h : i = i₀ <;> simp [Components.extend, h]
  map_smul' a x := by ext ⟨i, q⟩; by_cases h : i = i₀ <;> simp [Components.extend, h]

@[simp] theorem parity_embed (i₀ : I) (x : E → ZMod 2) :
    parity (embed i₀ x) = x := by
  ext q
  simp [parity, embed, Components.extend]

theorem parity_surjective (i₀ : I) : Function.Surjective (parity (I := I) (E := E)) :=
  fun x => ⟨embed i₀ x, parity_embed i₀ x⟩

theorem replicate_injective (i₀ : I) : Function.Injective (replicate (I := I) (E := E)) := by
  intro x y h
  funext q
  exact congrFun h (i₀, q)

@[simp] theorem embed_weight (i₀ : I) (x : E → ZMod 2) :
    hammingNorm (embed i₀ x) = hammingNorm x := Components.extend_weight i₀ x

theorem replicate_weight (x : E → ZMod 2) :
    hammingNorm (replicate (I := I) x) = Fintype.card I * hammingNorm x := by
  have hs : Finset.univ.filter (fun p : I × E => replicate x p ≠ 0) =
      Finset.univ ×ˢ (Finset.univ.filter (fun q : E => x q ≠ 0)) := by
    ext ⟨i, q⟩
    simp [replicate]
  change (Finset.univ.filter (fun p : I × E => replicate x p ≠ 0)).card = _
  rw [hs, Finset.card_product, Finset.card_univ]
  rfl

theorem parity_weight_le (x : I × E → ZMod 2) :
    hammingNorm (parity x) ≤ hammingNorm x := by
  classical
  let S := Finset.univ.filter (fun q : E => parity x q ≠ 0)
  let T := Finset.univ.filter (fun q : I × E => x q ≠ 0)
  have hs : S ⊆ T.image Prod.snd := by
    intro q hq
    have hq' : ∑ i, x (i, q) ≠ 0 := (Finset.mem_filter.mp hq).2
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq'
    exact Finset.mem_image.mpr ⟨(i, q), by simp [T, hi], rfl⟩
  exact (Finset.card_le_card hs).trans (Finset.card_image_le)

theorem dot_replicate (x : I × E → ZMod 2) (z : E → ZMod 2) :
    x ⬝ᵥ replicate z = parity x ⬝ᵥ z := by
  simp only [dotProduct, replicate, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, parity, Finset.sum_mul]
  exact Finset.sum_comm

theorem replicate_dot (z : E → ZMod 2) (x : I × E → ZMod 2) :
    replicate z ⬝ᵥ x = z ⬝ᵥ parity x := by
  rw [dotProduct_comm, dot_replicate, dotProduct_comm]

/-- Exact X distance is unchanged by a split parity extension. -/
theorem distance_comap (i₀ : I) (S U : Submodule (ZMod 2) (E → ZMod 2)) (d : ℕ)
    (h : Components.Distance S U d) :
    Components.Distance (S.comap (parity (I := I))) (U.comap parity) d := by
  obtain ⟨⟨x, hx, hn, hw⟩, hl⟩ := h
  refine ⟨⟨embed i₀ x, ?_, ?_, (embed_weight i₀ x).trans hw⟩, ?_⟩
  · simpa only [Submodule.mem_comap, parity_embed] using hx
  · simpa only [Submodule.mem_comap, parity_embed] using hn
  · intro y hy hn
    exact (hl (parity y) hy hn).trans (parity_weight_le y)

/-- Every replicateed logical has exactly r times its original physical weight. -/
theorem distance_map (i₀ : I) (S U : Submodule (ZMod 2) (E → ZMod 2)) (d : ℕ)
    (h : Components.Distance S U d) :
    Components.Distance (S.map (replicate (I := I))) (U.map replicate) (Fintype.card I * d) := by
  obtain ⟨⟨x, hx, hn, hw⟩, hl⟩ := h
  refine ⟨⟨replicate x, ⟨x, hx, rfl⟩, ?_, ?_⟩, ?_⟩
  · rintro ⟨y, hy, he⟩
    exact hn ((replicate_injective i₀ he) ▸ hy)
  · rw [replicate_weight, hw]
  · intro y hy hn
    obtain ⟨x, hx, rfl⟩ := hy
    have hnx : x ∉ U := fun hu => hn ⟨x, hu, rfl⟩
    rw [replicate_weight]
    exact Nat.mul_le_mul_left _ (hl x hx hnx)

/-- A star-edge check; the anchor's own edge is zero and may be omitted. -/
def pair (i₀ i : I) (q : E) : I × E → ZMod 2 :=
  Pi.single (i, q) 1 + Pi.single (i₀, q) 1

@[simp] theorem parity_pair (i₀ i : I) (q : E) : parity (pair i₀ i q) = 0 := by
  ext e
  by_cases h : e = q
  · subst e
    simp [parity, pair, Pi.single_apply, Prod.mk.injEq, Finset.sum_add_distrib,
      CharTwo.add_self_eq_zero]
  · simp [parity, pair, Pi.single_apply, Prod.mk.injEq, h]

theorem pair_dot (i₀ i : I) (q : E) (z : I × E → ZMod 2) :
    pair i₀ i q ⬝ᵥ z = z (i, q) + z (i₀, q) := by
  simp [pair, add_dotProduct]

/-- Explicit decomposition of the kernel, not a finite search for generators. -/
theorem pair_decomposition (i₀ : I) (x : I × E → ZMod 2) :
    ∑ i, ∑ q, x (i, q) • pair i₀ i q = x + embed i₀ (parity x) := by
  ext ⟨j, e⟩
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    pair, Pi.single_apply, Prod.mk.injEq, mul_add, Finset.sum_add_distrib]
  by_cases h : j = i₀
  · subst j
    simp [embed, Components.extend, parity, ite_and, eq_comm]
  · simp [embed, Components.extend, parity, h, ite_and, eq_comm]

/-- Explicit sparse X rows. -/
def HX (i₀ : I) (A : Matrix RX E (ZMod 2)) : Matrix (RX ⊕ (I × E)) (I × E) (ZMod 2)
  | .inl a => embed i₀ (A a)
  | .inr (i, q) => pair i₀ i q

/-- Explicit Z rows. -/
def HZ (B : Matrix RZ E (ZMod 2)) : Matrix RZ (I × E) (ZMod 2) := fun b => replicate (B b)

theorem rowspace_HZ (B : Matrix RZ E (ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (HZ (I := I) B)) =
      (Submodule.span (ZMod 2) (Set.range B)).map replicate := by
  rw [Submodule.map_span]
  congr 1
  ext x
  simp [HZ, Set.mem_image, Set.mem_range]

theorem rowspace_HX (i₀ : I) (A : Matrix RX E (ZMod 2)) :
    Submodule.span (ZMod 2) (Set.range (HX i₀ A)) =
      (Submodule.span (ZMod 2) (Set.range A)).comap parity := by
  let U := Submodule.span (ZMod 2) (Set.range A)
  let W := Submodule.span (ZMod 2) (Set.range (HX i₀ A))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    cases r with
    | inl a =>
      change parity (embed i₀ (A a)) ∈ U
      rw [parity_embed]
      exact Submodule.subset_span ⟨a, rfl⟩
    | inr p =>
      rcases p with ⟨i, q⟩
      change parity (pair i₀ i q) ∈ U
      rw [parity_pair]
      exact U.zero_mem
  · intro x hx
    have he : embed i₀ (parity x) ∈ W := by
      apply (show U ≤ W.comap (embed i₀) from ?_) hx
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    have hp : x + embed i₀ (parity x) ∈ W := by
      rw [← pair_decomposition]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.sum_mem
      intro q _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨Sum.inr (i, q), rfl⟩
    have hh := W.add_mem hp he
    have hz : embed i₀ (parity x) + embed i₀ (parity x) = 0 := by
      ext p
      exact CharTwo.add_self_eq_zero _
    simpa [add_assoc, hz] using hh

theorem kernel_HZ (B : Matrix RZ E (ZMod 2)) :
    LinearMap.ker (HZ (I := I) B).mulVecLin = (LinearMap.ker B.mulVecLin).comap parity := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Matrix.mulVecLin_apply,
    funext_iff, Pi.zero_apply, Matrix.mulVec, HZ, replicate_dot]

theorem kernel_HX (i₀ : I) (A : Matrix RX E (ZMod 2)) :
    LinearMap.ker (HX i₀ A).mulVecLin = (LinearMap.ker A.mulVecLin).map replicate := by
  ext z
  constructor
  · intro hz
    let x : E → ZMod 2 := fun q => z (i₀, q)
    have he : replicate x = z := by
      ext ⟨i, q⟩
      have h := congrFun hz (Sum.inr (i, q))
      change pair i₀ i q ⬝ᵥ z = 0 at h
      rw [pair_dot] at h
      change z (i₀, q) = z (i, q)
      simpa [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right h
    refine ⟨x, ?_, he⟩
    funext a
    have h := congrFun hz (Sum.inl a)
    change embed i₀ (A a) ⬝ᵥ z = 0 at h
    rw [← he, dot_replicate, parity_embed] at h
    exact h
  · rintro ⟨x, hx, rfl⟩
    funext a
    cases a with
    | inl a =>
      change embed i₀ (A a) ⬝ᵥ replicate x = 0
      rw [dot_replicate, parity_embed]
      exact congrFun hx a
    | inr p =>
      rcases p with ⟨i, q⟩
      change pair i₀ i q ⬝ᵥ replicate x = 0
      rw [dot_replicate, parity_pair, zero_dotProduct]

theorem commutation (i₀ : I) (A : Matrix RX E (ZMod 2))
    (B : Matrix RZ E (ZMod 2)) (h : A * B.transpose = 0) :
    HX i₀ A * (HZ (I := I) B).transpose = 0 := by
  ext a b
  change HX i₀ A a ⬝ᵥ replicate (B b) = 0
  rw [dot_replicate]
  cases a with
  | inl a =>
    change parity (embed i₀ (A a)) ⬝ᵥ B b = 0
    rw [parity_embed]
    exact congrFun (congrFun h a) b
  | inr p =>
    rcases p with ⟨i, q⟩
    change parity (pair i₀ i q) ⬝ᵥ B b = 0
    rw [parity_pair, zero_dotProduct]

/-- Family capstone: exact CSS sector distances for the displayed matrices. -/
theorem exact_distances (i₀ : I) (A : Matrix RX E (ZMod 2))
    (B : Matrix RZ E (ZMod 2)) (dX dZ : ℕ)
    (hX : Components.Distance (LinearMap.ker B.mulVecLin)
      (Submodule.span (ZMod 2) (Set.range A)) dX)
    (hZ : Components.Distance (LinearMap.ker A.mulVecLin)
      (Submodule.span (ZMod 2) (Set.range B)) dZ) :
    Components.Distance (LinearMap.ker (HZ (I := I) B).mulVecLin)
      (Submodule.span (ZMod 2) (Set.range (HX i₀ A))) dX ∧
    Components.Distance (LinearMap.ker (HX i₀ A).mulVecLin)
      (Submodule.span (ZMod 2) (Set.range (HZ (I := I) B))) (Fintype.card I * dZ) := by
  rw [kernel_HZ, rowspace_HX, kernel_HX, rowspace_HZ]
  exact ⟨distance_comap i₀ _ _ _ hX, distance_map i₀ _ _ _ hZ⟩

/-- The new X stabilizer splits as the old one and the parity kernel. -/
def comapEquiv (i₀ : I) (U : Submodule (ZMod 2) (E → ZMod 2)) :
    U.comap (parity (I := I)) ≃ₗ[ZMod 2] U × LinearMap.ker (parity (I := I) (E := E)) where
  toFun x := (⟨parity x.1, x.property⟩,
    ⟨x.1 + embed i₀ (parity x.1), by
      change parity (x.1 + embed i₀ (parity x.1)) = 0
      rw [map_add, parity_embed]
      ext q
      exact CharTwo.add_self_eq_zero _⟩)
  invFun p := ⟨embed i₀ p.1.1 + p.2.1, by
    change parity (embed i₀ p.1.1 + p.2.1) ∈ U
    rw [map_add, parity_embed, show parity p.2.1 = 0 from p.2.property, add_zero]
    exact p.1.property⟩
  left_inv x := by
    apply Subtype.ext
    change embed i₀ (parity x.1) + (x.1 + embed i₀ (parity x.1)) = x.1
    ext p
    simp [Pi.add_apply, add_left_comm, CharTwo.add_self_eq_zero]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change parity (embed i₀ p.1.1 + p.2.1) = p.1.1
      rw [map_add, parity_embed, show parity p.2.1 = 0 from p.2.property, add_zero]
    · apply Subtype.ext
      change (embed i₀ p.1.1 + p.2.1) + embed i₀ (parity (embed i₀ p.1.1 + p.2.1)) = p.2.1
      rw [map_add, parity_embed, show parity p.2.1 = 0 from p.2.property, add_zero]
      ext q
      simp only [Pi.add_apply]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact map_add parity _ _
    · change (x.1 + y.1) + embed i₀ (parity (x.1 + y.1)) =
        (x.1 + embed i₀ (parity x.1)) + (y.1 + embed i₀ (parity y.1))
      rw [map_add, map_add]
      abel
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact map_smul parity _ _
    · change (a • x.1) + embed i₀ (parity (a • x.1)) =
        a • (x.1 + embed i₀ (parity x.1))
      rw [map_smul, map_smul, smul_add]

theorem parity_kernel_rank (i₀ : I) :
    finrank (ZMod 2) (LinearMap.ker (parity (I := I) (E := E))) + Fintype.card E =
      Fintype.card I * Fintype.card E := by
  have h := LinearMap.finrank_range_add_finrank_ker (parity (I := I) (E := E))
  rw [LinearMap.range_eq_top.mpr (parity_surjective i₀)] at h
  simpa [add_comm] using h

theorem ranks (i₀ : I) (A : Matrix RX E (ZMod 2)) (B : Matrix RZ E (ZMod 2)) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (HX i₀ A))) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)) +
        (Fintype.card I * Fintype.card E - Fintype.card E) ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (HZ (I := I) B))) =
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range B)) := by
  constructor
  · rw [rowspace_HX, (comapEquiv i₀ _).finrank_eq, Module.finrank_prod]
    have h := parity_kernel_rank (E := E) i₀
    omega
  · rw [rowspace_HZ]
    exact (Submodule.equivMapOfInjective replicate (replicate_injective i₀) _).finrank_eq.symm

theorem encoded_dimension (i₀ : I) (A : Matrix RX E (ZMod 2))
    (B : Matrix RZ E (ZMod 2)) :
    Fintype.card I * Fintype.card E -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (HX i₀ A))) -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (HZ (I := I) B))) =
    Fintype.card E - finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range A)) -
      finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range B)) := by
  obtain ⟨hX, hZ⟩ := ranks i₀ A B
  rw [hX, hZ]
  have h := parity_kernel_rank (E := E) i₀
  omega

theorem pair_weight_le (i₀ i : I) (q : E) : hammingNorm (pair i₀ i q) ≤ 2 := by
  classical
  have hs : Finset.univ.filter (fun p => pair i₀ i q p ≠ 0) ⊆ {(i, q), (i₀, q)} := by
    intro p hp
    by_contra h
    have h' : p ≠ (i, q) ∧ p ≠ (i₀, q) := by simpa using h
    exact (Finset.mem_filter.mp hp).2 (by simp [pair, Pi.single_apply, h'.1, h'.2])
  exact (Finset.card_le_card hs).trans (by
    by_cases h : (i, q) = (i₀, q) <;> simp [h])

theorem row_weights (i₀ : I) (A : Matrix RX E (ZMod 2)) (B : Matrix RZ E (ZMod 2))
    (wX wZ : ℕ) (hX : ∀ a, hammingNorm (A a) ≤ wX)
    (hZ : ∀ b, hammingNorm (B b) ≤ wZ) :
    (∀ a, hammingNorm (HX i₀ A a) ≤ max wX 2) ∧
    (∀ b, hammingNorm (HZ (I := I) B b) ≤ Fintype.card I * wZ) := by
  constructor
  · intro a
    cases a with
    | inl a =>
      change hammingNorm (embed i₀ (A a)) ≤ _
      rw [embed_weight]
      exact (hX a).trans (le_max_left _ _)
    | inr p => exact (pair_weight_le i₀ p.1 p.2).trans (le_max_right _ _)
  · intro b
    change hammingNorm (replicate (I := I) (B b)) ≤ _
    rw [replicate_weight]
    exact Nat.mul_le_mul_left _ (hZ b)

theorem z_column_weight [Fintype RZ] (B : Matrix RZ E (ZMod 2)) (i : I) (q : E) :
    hammingNorm (fun b => HZ (I := I) B b (i, q)) = hammingNorm (fun b => B b q) := rfl

theorem x_column_weight_le [Fintype RX] (i₀ j : I) (A : Matrix RX E (ZMod 2)) (q : E) :
    hammingNorm (fun a => HX i₀ A a (j, q)) ≤
      hammingNorm (fun a => A a q) + Fintype.card I := by
  classical
  have hp : hammingNorm (fun p : I × E => pair i₀ p.1 p.2 (j, q)) ≤ Fintype.card I := by
    let T := Finset.univ.filter (fun p : I × E => pair i₀ p.1 p.2 (j, q) ≠ 0)
    have hs : T ⊆ Finset.univ ×ˢ {q} := by
      intro p hp
      have hq : p.2 = q := by
        by_contra he
        have hp' : (j, q) ≠ p := fun h => he (congrArg Prod.snd h).symm
        exact (Finset.mem_filter.mp hp).2
          (by simp [pair, Pi.single_apply, Prod.mk.injEq, he, Ne.symm he, hp'])
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hq⟩
    exact (Finset.card_le_card hs).trans (by simp)
  change (Finset.univ.filter (fun a => HX i₀ A a (j, q) ≠ 0)).card ≤ _
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  have he : (∑ a : RX, if HX i₀ A (Sum.inl a) (j, q) ≠ 0 then 1 else 0) ≤
      hammingNorm (fun a => A a q) := by
    by_cases h : j = i₀
    · simp [HX, embed, Components.extend, h, hammingNorm, Finset.card_filter]
    · simp [HX, embed, Components.extend, h]
  apply Nat.add_le_add he
  convert hp using 1
  rw [hammingNorm, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : pair i₀ p.1 p.2 (j, q) = 0 <;> simp [HX, h]

end QldpcVerification.QubitReplication
