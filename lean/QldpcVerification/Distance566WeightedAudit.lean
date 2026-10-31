import Lean.Elab.GuardMsgs
import QldpcVerification.Distance566WeightedPauli

/-! Focused guarded audit of the additive literal-target bound-six proof. -/

/-- info: 'QldpcVerification.WeightedPackingCertificates.weightedClassCheck_map_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.weightedClassCheck_map_sound

/-- info: 'QldpcVerification.WeightedPackingCertificates.packedClassCheck_map_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.packedClassCheck_map_sound

/-- info: 'QldpcVerification.WeightedPackingCertificates.rowMasksCheck_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.rowMasksCheck_sound

/-- info: 'QldpcVerification.WeightedPackingCertificates.mask_bound_of_rangeCheck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.mask_bound_of_rangeCheck

/-- info: 'QldpcVerification.WeightedPackingCertificates.decode_row_no_wrap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.decode_row_no_wrap

/-- info: 'QldpcVerification.WeightedPackingCertificates.rangeCheck_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.rangeCheck_append

/-- info: 'QldpcVerification.WeightedPackingCertificates.packedClassCheck_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.packedClassCheck_append

/-- info: 'QldpcVerification.WeightedPackingCertificates.capChunkCheck_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.WeightedPackingCertificates.capChunkCheck_append

/-- info: 'QldpcVerification.Distance566Weighted.RowData.x_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.RowData.x_check

/-- info: 'QldpcVerification.Distance566Weighted.RowData.z_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.RowData.z_check

/-- info: 'QldpcVerification.Distance566Weighted.xCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.xCoverage

/-- info: 'QldpcVerification.Distance566Weighted.zCoverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.zCoverage

/-- info: 'QldpcVerification.Distance566Weighted.detects_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.detects_X

/-- info: 'QldpcVerification.Distance566Weighted.detects_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.detects_Z

/-- info: 'QldpcVerification.Distance566Weighted.x_family_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.x_family_class

/-- info: 'QldpcVerification.Distance566Weighted.z_family_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.z_family_class

/-- info: 'QldpcVerification.Distance566Weighted.lower_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.lower_X

/-- info: 'QldpcVerification.Distance566Weighted.lower_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.lower_Z

/-- info: 'QldpcVerification.Distance566Weighted.partial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.partial_bounds

/-- info: 'QldpcVerification.Distance566Weighted.pauli_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.pauli_lower

/-- info: 'QldpcVerification.Distance566Weighted.X_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.X_upper_witness

/-- info: 'QldpcVerification.Distance566Weighted.pauli_upper_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.pauli_upper_witness

/-- info: 'QldpcVerification.Distance566Weighted.Checks.xSupports_range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.xSupports_range

/-- info: 'QldpcVerification.Distance566Weighted.Checks.zSupports_range' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.zSupports_range

/-- info: 'QldpcVerification.Distance566Weighted.Checks.xMasks_range' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.xMasks_range

/-- info: 'QldpcVerification.Distance566Weighted.Checks.zMasks_range' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.zMasks_range

/-- info: 'QldpcVerification.Distance566Weighted.Checks.xPairedMasks_range' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.xPairedMasks_range

/-- info: 'QldpcVerification.Distance566Weighted.Checks.zPairedMasks_range' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.Checks.zPairedMasks_range

/-- info: 'QldpcVerification.Distance566Weighted.PackingData.xRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.PackingData.xRange

/-- info: 'QldpcVerification.Distance566Weighted.PackingData.zRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.Distance566Weighted.PackingData.zRange

open QldpcVerification.WeightedPackingCertificates in
example : rangeCheck 2 1 [((1, [0]), 9)] = true := by decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : rangeCheck 2 1 [((1, [1]), 9)] = false := by decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : rangeCheck 2 1 [((4, []), 9)] = false := by decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : rowMasksCheck ([{0, 1}] : List (Finset (Fin 2))) (fun _ => 3) = true := by
  decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : rowMasksCheck ([{0, 1}] : List (Finset (Fin 2))) (fun _ => 1) = false := by
  decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : packedClassCheck (fun _ : Fin 1 => 3) 1 [((2, [⟨0, by decide⟩]), 9)] = true := by
  decide +kernel

open QldpcVerification.WeightedPackingCertificates in
example : packedClassCheck (fun _ : Fin 1 => 3) 1 [((2, []), 9)] = false := by decide +kernel

open QldpcVerification.Input.Sparse in
example : capCheck 2 [(1, 5), (2, 1)] 4 = false := by decide +kernel

open QldpcVerification.Input.Sparse in
example : capCheck 2 [(1, 5), (2, 1)] 5 = true := by decide +kernel
