import QldpcVerification.WeightedPackingCertificates

/-!
Finite mixed-class packing checks. Each representative records its own base
index and original-row witness; natural weights remain unexpanded. Pair checks
here concern the base supports. Transferring them to representatives additionally
requires the reference to annihilate the checked row space.
-/

namespace QldpcVerification.SectorPackingCertificates

open Matrix Input Input.Sparse Distance566Certificates

abbrev RawMixedRep := ℕ × WeightedPackingCertificates.RawRep
abbrev MixedRep (b m : ℕ) := Fin b × WeightedPackingCertificates.Rep m

def decodeMixed {b m : ℕ} [NeZero b] [NeZero m] (r : RawMixedRep) : MixedRep b m :=
  (Fin.ofNat b r.1, WeightedPackingCertificates.decode r.2)

def mixedFamily {b m : ℕ} (reps : List (MixedRep b m)) : List (ℕ × ℕ) :=
  reps.map fun r => (r.2.1.1, r.2.2)

/-- The complete entry associated with an index into its mask/weight projection. -/
def entryAt {b m : ℕ} (reps : List (MixedRep b m))
    (i : Fin (mixedFamily reps).length) : MixedRep b m :=
  reps.get ⟨i, by simpa only [mixedFamily, List.length_map] using i.isLt⟩

theorem mixedFamily_get {b m : ℕ} (reps : List (MixedRep b m))
    (i : Fin (mixedFamily reps).length) :
    (mixedFamily reps).get i = ((entryAt reps i).2.1.1, (entryAt reps i).2.2) := by
  simp only [mixedFamily, entryAt, List.get_eq_getElem, List.getElem_map]

theorem entryAt_mem {b m : ℕ} (reps : List (MixedRep b m))
    (i : Fin (mixedFamily reps).length) : entryAt reps i ∈ reps :=
  List.get_mem reps _

def mixedRangeCheck (n b m : ℕ) (reps : List RawMixedRep) : Bool :=
  reps.all fun r => decide (r.1 < b) && WeightedPackingCertificates.rangeCheck n m [r.2]

theorem mixedRangeCheck_append (n b m : ℕ) (a c : List RawMixedRep) :
    mixedRangeCheck n b m (a ++ c) =
      (mixedRangeCheck n b m a && mixedRangeCheck n b m c) := by
  simp only [mixedRangeCheck, List.all_append]

theorem rawRep_range_of_mixedRangeCheck {n b m : ℕ} {reps : List RawMixedRep}
    (h : mixedRangeCheck n b m reps = true) {r : RawMixedRep} (hr : r ∈ reps) :
    WeightedPackingCertificates.rangeCheck n m [r.2] = true := by
  have hh := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hh
  exact hh.2

theorem decodeMixed_base_no_wrap {n b m : ℕ} [NeZero b] [NeZero m]
    {reps : List RawMixedRep} (h : mixedRangeCheck n b m reps = true)
    {r : RawMixedRep} (hr : r ∈ reps) : (decodeMixed (b := b) (m := m) r).1.val = r.1 := by
  have hh := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hh
  exact Nat.mod_eq_of_lt (of_decide_eq_true hh.1)

theorem decodeMixed_row_no_wrap {n b m : ℕ} [NeZero b] [NeZero m]
    {reps : List RawMixedRep} (h : mixedRangeCheck n b m reps = true)
    {r : RawMixedRep} (hr : r ∈ reps) {j : ℕ} (hj : j ∈ r.2.1.2) :
    (Fin.ofNat m j).val = j :=
  WeightedPackingCertificates.decode_row_no_wrap
    (rawRep_range_of_mixedRangeCheck h hr) (by simp) hj

theorem mixed_mask_bound_of_rangeCheck {n b m : ℕ} {reps : List RawMixedRep}
    (h : mixedRangeCheck n b m reps = true) {r : RawMixedRep} (hr : r ∈ reps) :
    r.2.1.1 < 2 ^ n :=
  WeightedPackingCertificates.mask_bound_of_rangeCheck
    (rawRep_range_of_mixedRangeCheck h hr) (by simp)

def mixedClassCheck {b m : ℕ} (masks : Fin m → ℕ) (bases : Fin b → ℕ)
    (reps : List (MixedRep b m)) : Bool :=
  reps.all fun r => WeightedPackingCertificates.packedClassCheck masks (bases r.1) [r.2]

theorem mixedClassCheck_append {b m : ℕ} (masks : Fin m → ℕ) (bases : Fin b → ℕ)
    (a c : List (MixedRep b m)) : mixedClassCheck masks bases (a ++ c) =
      (mixedClassCheck masks bases a && mixedClassCheck masks bases c) := by
  simp only [mixedClassCheck, List.all_append]

/-- A checked mixed representative differs from its own base by actual matrix rows. -/
theorem mixedClassCheck_map_sound {n b : ℕ} (rows : List (Finset (Fin n)))
    (masks : Fin rows.length → ℕ)
    (hmasks : WeightedPackingCertificates.rowMasksCheck rows masks = true)
    (bases : Fin b → ℕ) (reps : List (MixedRep b rows.length))
    (h : mixedClassCheck masks bases reps = true) (i : Fin (mixedFamily reps).length) :
    vec n ((mixedFamily reps).get i).1 - vec n (bases (entryAt reps i).1) ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
  have hc := List.all_eq_true.mp h (entryAt reps i) (entryAt_mem reps i)
  have hs := WeightedPackingCertificates.packedClassCheck_map_sound rows masks hmasks
    (bases (entryAt reps i).1) [(entryAt reps i).2] hc
    ⟨0, by simp [WeightedPackingCertificates.family]⟩
  rw [mixedFamily_get]
  simpa only [WeightedPackingCertificates.family, List.map_cons, List.map_nil,
    List.get_eq_getElem, List.getElem_cons_zero] using hs

def mixedPairCheck {n b m : ℕ} (baseSupports : Fin b → Finset (Fin n))
    (reference : ℕ) (reps : List (MixedRep b m)) : Bool :=
  reps.all fun r => parity (baseSupports r.1) reference

theorem mixedPairCheck_append {n b m : ℕ} (baseSupports : Fin b → Finset (Fin n))
    (reference : ℕ) (a c : List (MixedRep b m)) :
    mixedPairCheck baseSupports reference (a ++ c) =
      (mixedPairCheck baseSupports reference a && mixedPairCheck baseSupports reference c) := by
  simp only [mixedPairCheck, List.all_append]

theorem mixedPairCheck_parity {n b m : ℕ} (baseSupports : Fin b → Finset (Fin n))
    (reference : ℕ) (reps : List (MixedRep b m))
    (h : mixedPairCheck baseSupports reference reps = true)
    (i : Fin (mixedFamily reps).length) :
    parity (baseSupports (entryAt reps i).1) reference = true :=
  List.all_eq_true.mp h (entryAt reps i) (entryAt_mem reps i)

/-- This pairing is with the base. Row-space annihilation is needed for transfer. -/
theorem mixedPairCheck_sound {n b m : ℕ} (baseSupports : Fin b → Finset (Fin n))
    (reference : ℕ) (reps : List (MixedRep b m))
    (h : mixedPairCheck baseSupports reference reps = true)
    (i : Fin (mixedFamily reps).length) :
    vec n reference ⬝ᵥ indicator (baseSupports (entryAt reps i).1) = 1 := by
  rw [dotProduct_comm, indicator_dot, mixedPairCheck_parity baseSupports reference reps h i]
  rfl

def patternCheck {n : ℕ} (supports : List (Finset (Fin n)))
    (reference expected : ℕ) : Bool :=
  allIdx (fun j s => parity s reference == bit expected j) supports 0

theorem pattern_of_check {n : ℕ} (supports : List (Finset (Fin n)))
    (reference expected : ℕ) (h : patternCheck supports reference expected = true)
    (i : Fin supports.length) :
    vec n reference ⬝ᵥ indicator (supports.get i) = if bit expected i then 1 else 0 := by
  rw [dotProduct_comm, indicator_dot]
  have hh := allIdx_spec _ supports 0 h i
  simp only [Nat.zero_add] at hh
  rw [beq_iff_eq.mp hh]

end QldpcVerification.SectorPackingCertificates
