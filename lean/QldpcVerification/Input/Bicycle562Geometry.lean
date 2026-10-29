import QldpcVerification.Lattice.IncidenceRank
import QldpcVerification.Input.SparseCertificates
import QldpcVerification.Input.Bicycle562Data

/-! The original rows are incidence rows of two cyclic square-lattice graphs. -/

namespace QldpcVerification.Bicycle562Geometry

open Matrix Input.Sparse Bicycle562Data Lattice

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def blockEquiv : (ZMod 281 ⊕ ZMod 281) ≃ Fin 562 := finSumFinEquiv

def horizontal (q : Fin 562) : Bool :=
  match blockEquiv.symm q with
  | .inl _ => true
  | .inr _ => false

def xSource (q : Fin 562) : ZMod 281 :=
  match blockEquiv.symm q with
  | .inl r => r - 165
  | .inr r => r - 280

def xTarget (q : Fin 562) : ZMod 281 :=
  match blockEquiv.symm q with
  | .inl r => r - 158
  | .inr r => r - 135

def zSource (q : Fin 562) : ZMod 281 :=
  match blockEquiv.symm q with
  | .inl r => r - 146
  | .inr r => r - 123

def zTarget (q : Fin 562) : ZMod 281 :=
  match blockEquiv.symm q with
  | .inl r => r - 1
  | .inr r => r - 116

def xStar (v : ZMod 281) : Finset (Fin 562) :=
  {blockEquiv (.inl (v + 158)), blockEquiv (.inl (v + 165)),
   blockEquiv (.inr (v + 135)), blockEquiv (.inr (v + 280))}

def zStar (v : ZMod 281) : Finset (Fin 562) :=
  {blockEquiv (.inl (v + 1)), blockEquiv (.inl (v + 146)),
   blockEquiv (.inr (v + 116)), blockEquiv (.inr (v + 123))}

theorem x_step (q : Fin 562) : xTarget q - xSource q = if horizontal q then 7 else 145 := by
  obtain ⟨e, rfl⟩ := blockEquiv.surjective q
  cases e <;> simp [horizontal, xSource, xTarget] <;> ring

theorem z_step (q : Fin 562) : zTarget q - zSource q = if horizontal q then 145 else 7 := by
  obtain ⟨e, rfl⟩ := blockEquiv.surjective q
  cases e <;> simp [horizontal, zSource, zTarget] <;> ring

theorem x_connected (f : ZMod 281 → ZMod 2)
    (h : ∀ e, f (xSource e) = f (xTarget e)) : ∀ v, f v = f 0 := by
  intro v
  apply constant_of_periodic f (7 : ZMod 281) 241 (by decide) (fun w => ?_) v
  have hh := h (blockEquiv (.inl (w + 165)))
  have hs : xSource (blockEquiv (.inl (w + 165))) = w := by
    simp only [xSource, Equiv.symm_apply_apply]
    ring
  have ht : xTarget (blockEquiv (.inl (w + 165))) = w + 7 := by
    simp only [xTarget, Equiv.symm_apply_apply]
    ring
  rw [hs, ht] at hh
  exact hh.symm

theorem z_connected (f : ZMod 281 → ZMod 2)
    (h : ∀ e, f (zSource e) = f (zTarget e)) : ∀ v, f v = f 0 := by
  intro v
  apply constant_of_periodic f (7 : ZMod 281) 241 (by decide) (fun w => ?_) v
  have hh := h (blockEquiv (.inr (w + 123)))
  have hs : zSource (blockEquiv (.inr (w + 123))) = w := by
    simp only [zSource, Equiv.symm_apply_apply]
    ring
  have ht : zTarget (blockEquiv (.inr (w + 123))) = w + 7 := by
    simp only [zTarget, Equiv.symm_apply_apply]
    ring
  rw [hs, ht] at hh
  exact hh.symm

theorem x_no_loop (q : Fin 562) : xSource q ≠ xTarget q := by
  intro h
  have hh := x_step q
  rw [h, sub_self] at hh
  have hn : ∀ b : Bool, (if b then (7 : ZMod 281) else 145) ≠ 0 := by decide
  exact hn _ hh.symm

theorem z_no_loop (q : Fin 562) : zSource q ≠ zTarget q := by
  intro h
  have hh := z_step q
  rw [h, sub_self] at hh
  have hn : ∀ b : Bool, (if b then (145 : ZMod 281) else 7) ≠ 0 := by decide
  exact hn _ hh.symm

theorem x_mem_star (v : ZMod 281) (q : Fin 562) :
    q ∈ xStar v ↔ xSource q = v ∨ xTarget q = v := by
  obtain ⟨e, rfl⟩ := blockEquiv.surjective q
  cases e <;> simp [xStar, xSource, xTarget, sub_eq_iff_eq_add, or_comm]

theorem z_mem_star (v : ZMod 281) (q : Fin 562) :
    q ∈ zStar v ↔ zSource q = v ∨ zTarget q = v := by
  obtain ⟨e, rfl⟩ := blockEquiv.surjective q
  cases e <;> simp [zStar, zSource, zTarget, sub_eq_iff_eq_add, or_comm]

theorem indicator_incidence {E V : Type} [DecidableEq V]
    (s t : E → V) (e : E) (v : V) (hne : s e ≠ t e) :
    (if s e = v ∨ t e = v then (1 : ZMod 2) else 0) = incidence s t e v := by
  by_cases hs : s e = v <;> by_cases ht : t e = v
  · exact (hne (hs.trans ht.symm)).elim
  · simp [incidence, hs, ht]
  · simp [incidence, hs, ht]
  · simp [incidence, hs, ht]

theorem x_indicator (v : ZMod 281) (q : Fin 562) :
    indicator (xStar v) q = incidence xSource xTarget q v := by
  simpa only [indicator, x_mem_star] using indicator_incidence _ _ _ _ (x_no_loop q)

theorem z_indicator (v : ZMod 281) (q : Fin 562) :
    indicator (zStar v) q = incidence zSource zTarget q v := by
  simpa only [indicator, z_mem_star] using indicator_incidence _ _ _ _ (z_no_loop q)

theorem x_match : ∀ i : Fin 281, hx.get i = xStar i := by decide +kernel
theorem z_match : ∀ i : Fin 281, hz.get i = zStar i := by decide +kernel

theorem block_labels : ∀ q : Fin 562,
    (vec 562 (blockMasks.get ⟨0, by decide⟩) q,
     vec 562 (blockMasks.get ⟨1, by decide⟩) q) = axisLabel horizontal q := by
  decide +kernel

theorem horizontal_val (q : Fin 562) : horizontal q = decide (q.val < 281) := by
  obtain ⟨e, rfl⟩ := blockEquiv.surjective q
  cases e with
  | inl r =>
    simp [horizontal, blockEquiv]
    change (r : Fin 281).val < 281
    exact r.isLt
  | inr r =>
    simp [horizontal, blockEquiv]
    change 281 ≤ 281 + (r : Fin 281).val
    omega

theorem blocks_vector (i : Fin 2) : vec 562 (blockMasks.get i) = indicator (blocks.get i) := by
  funext q
  have h := block_labels q
  have hv := horizontal_val q
  fin_cases i
  · have hh := congrArg Prod.fst h
    simpa [blocks, indicator, axisLabel, axisX, hv] using hh
  · have hh := congrArg Prod.snd h
    by_cases hq : q.val < 281
    · simpa [blocks, indicator, axisLabel, axisY, hv, hq, Nat.not_le_of_gt hq] using hh
    · simpa [blocks, indicator, axisLabel, axisY, hv, hq, Nat.le_of_not_gt hq] using hh

-- The four branches use different subsets of the coordinate rewrite lemmas.
set_option linter.unusedSimpArgs false in
theorem blocks_paired (i j : Fin 2) :
    vec 562 (blockMasks.get i) ⬝ᵥ vec 562 (blockMasks.get j) = if i = j then 1 else 0 := by
  have h0 : vec 562 (blockMasks.get ⟨0, by decide⟩) =
      fun q => (axisLabel horizontal q).1 := funext fun q => congrArg Prod.fst (block_labels q)
  have h1 : vec 562 (blockMasks.get ⟨1, by decide⟩) =
      fun q => (axisLabel horizontal q).2 := funext fun q => congrArg Prod.snd (block_labels q)
  fin_cases i <;> fin_cases j
  all_goals
    simp only [h0, h1, dotProduct]
    rw [← blockEquiv.sum_comp]
    simp [Fintype.sum_sum_type, axisLabel, axisX, axisY, horizontal]
  all_goals decide

def qubitShift (v : ZMod 281) : Fin 562 ≃ Fin 562 :=
  blockEquiv.symm.trans ((Equiv.sumCongr (Equiv.addLeft v) (Equiv.addLeft v)).trans blockEquiv)

theorem shift_xStar (v w : ZMod 281) : (xStar w).image (qubitShift v) = xStar (v + w) := by
  simp [xStar, qubitShift, add_assoc]

theorem shift_zStar (v w : ZMod 281) : (zStar w).image (qubitShift v) = zStar (v + w) := by
  simp [zStar, qubitShift, add_assoc]

theorem comm_at_zero : ∀ w : Fin 281, ((xStar 0 ∩ zStar w).card % 2) = 0 := by
  decide +kernel

theorem comm_card (v w : ZMod 281) : (xStar v ∩ zStar w).card % 2 = 0 := by
  have hx : xStar v = (xStar 0).image (qubitShift v) := by simp [shift_xStar]
  have hz : zStar w = (zStar (w - v)).image (qubitShift v) := by
    rw [shift_zStar]
    congr 1
    abel
  rw [hx, hz, ← Finset.image_inter _ _ (qubitShift v).injective,
    Finset.card_image_of_injective _ (qubitShift v).injective]
  exact comm_at_zero (w - v)

theorem commutation : matrix hx * (matrix hz).transpose = 0 := by
  ext i j
  change indicator (hx.get i) ⬝ᵥ indicator (hz.get j) = 0
  rw [x_match, z_match, indicator_dot_indicator, ← ZMod.natCast_mod _ 2, comm_card]
  rfl

end QldpcVerification.Bicycle562Geometry
