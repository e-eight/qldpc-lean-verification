import Lean.Elab.GuardMsgs
import QldpcVerification.SectorPackingExamples

/-! Guarded axiom checks and small negative controls for conditional packing. -/

open QldpcVerification.SectorPacking.Examples
open Matrix

-- Strict rounding: six copies at capacity one cannot certify seven.
#guard ((7 - 1 : ℕ) * 1 < 7)
#guard !((7 - 1 : ℕ) * 1 < 6)
#guard !((2 - 1 : ℕ) * 0 < 0)

-- The valid mixed family loads each physical qubit once.
#guard (∀ q : Fin 2,
  (∑ i : Fin 2, if unitVector i q ≠ 0 then (1 : ℕ) else 0) = 1)
#guard !(∀ q : Fin 2,
  (∑ i : Fin 2, if unitVector i q ≠ 0 then (1 : ℕ) else 0) ≤ 0)

-- Wrong pairing and omitted sum sectors must fail, despite basis pairings.
#guard ((![0, 1] : Vec) ⬝ᵥ unitVector 0 = 0)
#guard !(∀ i : Fin 2, (![0, 1] : Vec) ⬝ᵥ unitVector i = 1)
#guard !(∀ c : Vec, c ≠ 0 → c = unitVector 0 ∨ c = unitVector 1)
#guard ((unitVector 0 + unitVector 1) ⬝ᵥ (![1, 1] : Vec) = 0)
#guard (Fintype.card {c : Fin 3 → ZMod 2 // c ≠ 0} = 7)

/--
info: 'QldpcVerification.SectorPacking.pairing_eq_of_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.pairing_eq_of_coordinates

/--
info: 'QldpcVerification.SectorPacking.weight_ge_of_sector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.weight_ge_of_sector

/--
info: 'QldpcVerification.SectorPacking.Certificate.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Certificate.lower_bound

/--
info: 'QldpcVerification.SectorPacking.coordinates_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.coordinates_ne_zero

/--
info: 'QldpcVerification.SectorPacking.weight_ge_of_coordinate_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.weight_ge_of_coordinate_cover

/--
info: 'QldpcVerification.SectorPacking.residual_pattern_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.residual_pattern_count

/--
info: 'QldpcVerification.SectorPacking.eq_residualCoordinates' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.eq_residualCoordinates

/--
info: 'QldpcVerification.SectorPacking.suffix_ne_zero' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.suffix_ne_zero

/--
info: 'QldpcVerification.SectorPacking.prefix_or_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.prefix_or_residual

/--
info: 'QldpcVerification.SectorPacking.weight_ge_of_prefix_sectors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.weight_ge_of_prefix_sectors

/--
info: 'QldpcVerification.SectorPacking.Homological.chain_weight_ge_of_sector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Homological.chain_weight_ge_of_sector

/--
info: 'QldpcVerification.SectorPacking.Homological.dual_chain_weight_ge_of_sector' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Homological.dual_chain_weight_ge_of_sector

/--
info: 'QldpcVerification.SectorPacking.Examples.coordinates_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.coordinates_eq

/--
info: 'QldpcVerification.SectorPacking.Examples.mixed_classes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.mixed_classes

/--
info: 'QldpcVerification.SectorPacking.Examples.sector11_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.sector11_lower_bound

/--
info: 'QldpcVerification.SectorPacking.Examples.singleton_threshold_fails' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.singleton_threshold_fails

/--
info: 'QldpcVerification.SectorPacking.Examples.global_bound_two_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.global_bound_two_false

/--
info: 'QldpcVerification.SectorPacking.Examples.zero_check_distance_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.zero_check_distance_one

/--
info: 'QldpcVerification.SectorPacking.Examples.prefix_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.prefix_assembly

/--
info: 'QldpcVerification.SectorPacking.Examples.missing_annihilation_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.missing_annihilation_counterexample

/--
info: 'QldpcVerification.SectorPacking.Examples.missing_annihilation_weight_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.missing_annihilation_weight_one

/--
info: 'QldpcVerification.SectorPacking.Examples.wrong_sector_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.wrong_sector_pairing

/--
info: 'QldpcVerification.SectorPacking.Examples.basis_residues_not_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.basis_residues_not_exhaustive

/--
info: 'QldpcVerification.SectorPacking.Examples.basis_pairings_do_not_cover_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.basis_pairings_do_not_cover_sum

/--
info: 'QldpcVerification.SectorPacking.Examples.three_residual_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPacking.Examples.three_residual_bits

