import QldpcVerification.SectorPacking

/-! Two physical qubits, no checks: mixed classes bound one sector, not the code. -/

namespace QldpcVerification.SectorPacking.Examples

open Matrix

abbrev Vec := Fin 2 → ZMod 2

def unitVector (i : Fin 2) : Vec := Pi.single i 1

/-- The zero-check code has two complete logical coordinates and no boundaries. -/
def zeroCheckCoverage : CoverageCertificate
    (⊤ : Submodule (ZMod 2) Vec) ⊥ 2 where
  boundary_le := bot_le
  detectors := unitVector
  witnesses := unitVector
  witness_mem := fun _ => Submodule.mem_top
  boundary_zero := by
    intro b hb j
    have hb0 : b = 0 := hb
    simp [hb0]
  paired := by decide
  dimension_bound := by simp

theorem coordinates_eq (x : Vec) :
    zeroCheckCoverage.coordinates ⟨x, Submodule.mem_top⟩ = x := by
  ext j
  simp [CoverageCertificate.coordinates, pairingMap, zeroCheckCoverage, unitVector]

/-- The two unit detectors belong to distinct logical classes. -/
theorem mixed_classes : unitVector 0 - unitVector 1 ∉
    (⊥ : Submodule (ZMod 2) Vec) := by
  change unitVector 0 - unitVector 1 ≠ 0
  decide

/-- Combining those classes gives total weight two at capacity one for sector 11. -/
def sector11 : Certificate zeroCheckCoverage ![1, 1] 2 where
  size := 2
  reference := ⟨![1, 1], Submodule.mem_top⟩
  reference_coordinates := coordinates_eq _
  representatives := unitVector
  weights := fun _ => 1
  cap := 1
  boundary_zero := by
    intro i b hb
    have hb0 : b = 0 := hb
    simp [hb0]
  pairs_one := by decide
  capacity := by decide
  threshold := by decide

theorem sector11_lower_bound (x : Vec)
    (hc : zeroCheckCoverage.coordinates ⟨x, Submodule.mem_top⟩ = ![1, 1]) :
    2 ≤ hammingNorm x := sector11.lower_bound Submodule.mem_top hc

/-- Either singleton family has weight/capacity one and cannot certify two. -/
theorem singleton_threshold_fails : ¬ ((2 - 1 : ℕ) * 1 < 1) := by decide

/-- A different sector still contains a nontrivial physical vector of weight one. -/
theorem global_bound_two_false :
    ¬ (∀ x : Vec, x ∈ (⊤ : Submodule (ZMod 2) Vec) →
      x ∉ (⊥ : Submodule (ZMod 2) Vec) → 2 ≤ hammingNorm x) := by
  intro h
  have hnonzero : unitVector 0 ∉ (⊥ : Submodule (ZMod 2) Vec) := by
    change unitVector 0 ≠ 0
    decide
  have hlower := h (unitVector 0) Submodule.mem_top hnonzero
  have hweight : hammingNorm (unitVector 0) = 1 := by decide
  omega

/-- In the same physical model, the global nontrivial-cycle distance is one. -/
theorem zero_check_distance_one :
    (∃ x : Vec, x ∉ (⊥ : Submodule (ZMod 2) Vec) ∧ hammingNorm x = 1) ∧
      ∀ x : Vec, x ∉ (⊥ : Submodule (ZMod 2) Vec) → 1 ≤ hammingNorm x := by
  constructor
  · refine ⟨unitVector 0, ?_, by decide⟩
    change unitVector 0 ≠ 0
    decide
  · intro x hx
    have hne : x ≠ 0 := by simpa using hx
    have hw : hammingNorm x ≠ 0 := hammingNorm_ne_zero_iff.mpr hne
    omega

/-- A singleton certificate for the other nonzero suffix in a one-bit split. -/
def sector01 : Certificate zeroCheckCoverage ![0, 1] 1 where
  size := 1
  reference := ⟨![0, 1], Submodule.mem_top⟩
  reference_coordinates := coordinates_eq _
  representatives := fun _ => unitVector 1
  weights := fun _ => 1
  cap := 1
  boundary_zero := by
    intro i b hb
    have hb0 : b = 0 := hb
    simp [hb0]
  pairs_one := by decide
  capacity := by decide
  threshold := by decide

/-- Exercise the prefix/suffix API: one good coordinate plus every nonzero suffix. -/
theorem prefix_assembly :
    ∀ x : Vec, x ∈ (⊤ : Submodule (ZMod 2) Vec) →
      x ∉ (⊥ : Submodule (ZMod 2) Vec) → 1 ≤ hammingNorm x := by
  apply weight_ge_of_prefix_sectors (r := 1) (s := 1) zeroCheckCoverage 1
  · intro x _ hb _ _
    exact zero_check_distance_one.2 x hb
  · intro tail htail
    have hcases : ∀ t : Fin 1 → ZMod 2, t ≠ 0 → t = ![1] := by decide
    have ht := hcases tail htail
    subst tail
    convert sector01 using 1; decide

/-- One reference pairing without boundary annihilation does not transfer. -/
theorem missing_annihilation_counterexample :
    ∃ r x z : Vec, r ⬝ᵥ z = 1 ∧ x ⬝ᵥ z = 0 ∧
      x - r ∈ (⊤ : Submodule (ZMod 2) Vec) := by
  exact ⟨unitVector 0, 0, unitVector 0, by decide, by decide, Submodule.mem_top⟩

/-- Second-bit coordinates have kernel `{0,e0}`. Reference 11 and cycle 01
have equal coordinates, but the first detector does not annihilate that kernel.
Both detectors pair with the reference; the weight-one cycle misses the first. -/
theorem missing_annihilation_weight_one :
    (∀ y : Vec, y 1 = 0 ↔ y = 0 ∨ y = unitVector 0) ∧
    (![1, 1] : Vec) 1 = (![0, 1] : Vec) 1 ∧
    (![0, 1] : Vec) - ![1, 1] = unitVector 0 ∧
    unitVector 0 ⬝ᵥ unitVector 0 = 1 ∧
    (∀ i : Fin 2, (![1, 1] : Vec) ⬝ᵥ unitVector i = 1) ∧
    (![0, 1] : Vec) ⬝ᵥ unitVector 0 = 0 ∧
    hammingNorm (![0, 1] : Vec) = 1 := by decide

/-- A detector valid for 11 need not pair to one with the sector 01. -/
theorem wrong_sector_pairing :
    (![0, 1] : Vec) ⬝ᵥ unitVector 0 = 0 := by decide

/-- Basis residues alone omit their nonzero sum. -/
theorem basis_residues_not_exhaustive :
    ∃ c : Vec, c ≠ 0 ∧ c ≠ unitVector 0 ∧ c ≠ unitVector 1 := by
  exact ⟨![1, 1], by decide, by decide, by decide⟩

/-- A detector pairing to one with both basis residues pairs to zero with their sum. -/
theorem basis_pairings_do_not_cover_sum :
    unitVector 0 ⬝ᵥ (![1, 1] : Vec) = 1 ∧
    unitVector 1 ⬝ᵥ (![1, 1] : Vec) = 1 ∧
    (unitVector 0 + unitVector 1) ⬝ᵥ (![1, 1] : Vec) = 0 := by decide

/-- Three residual bits have seven nonzero patterns, not three. -/
theorem three_residual_bits :
    Fintype.card {c : Fin 3 → ZMod 2 // c ≠ 0} = 7 := by decide

end QldpcVerification.SectorPacking.Examples
