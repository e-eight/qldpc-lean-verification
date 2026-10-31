import Lean.Elab.GuardMsgs
import QldpcVerification.SectorPackingCertificates

open QldpcVerification.SectorPackingCertificates
open QldpcVerification.Input.Sparse

-- A base index and every row index must be in range before finite decoding.
#guard mixedRangeCheck 2 2 1 [(0, ((1, []), 1)), (1, ((1, [0]), 2))]
#guard !(mixedRangeCheck 2 2 1 [(2, ((1, []), 1))])
#guard !(mixedRangeCheck 2 2 1 [(0, ((4, []), 1))])
#guard !(mixedRangeCheck 2 2 1 [(0, ((1, [1]), 1))])

-- Mixed entries keep their own base, row witness, and unexpanded weight.
#guard mixedFamily
  ([(0, ((1, []), 1)), (1, ((1, [0]), 2))].map (decodeMixed (b := 2) (m := 1))) =
    [(1, 1), (1, 2)]
#guard mixedClassCheck ![3] ![1, 2]
  ([(0, ((1, []), 1)), (1, ((1, [0]), 2))].map (decodeMixed (b := 2) (m := 1)))
#guard !(mixedClassCheck ![3] ![1, 2]
  ([(0, ((1, []), 1)), (1, ((2, [0]), 2))].map (decodeMixed (b := 2) (m := 1))))

-- Both bases pair with reference 11. A zero reference must fail.
#guard mixedPairCheck ![({0} : Finset (Fin 2)), {1}] 3
  ([(0, ((1, []), 1)), (1, ((1, [0]), 2))].map (decodeMixed (b := 2) (m := 1)))
#guard !(mixedPairCheck ![({0} : Finset (Fin 2)), {1}] 0
  ([(0, ((1, []), 1)), (1, ((1, [0]), 2))].map (decodeMixed (b := 2) (m := 1))))

-- The expected logical mask fixes the bit order, including zero coordinates.
#guard patternCheck [({0} : Finset (Fin 2)), {1}] 3 3
#guard !(patternCheck [({0} : Finset (Fin 2)), {1}] 3 1)
#guard patternCheck [({0} : Finset (Fin 2)), {1}] 0 0


/--
info: 'QldpcVerification.SectorPackingCertificates.mixedFamily_get' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedFamily_get

/--
info: 'QldpcVerification.SectorPackingCertificates.entryAt_mem' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.entryAt_mem

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedRangeCheck_append' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedRangeCheck_append

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedClassCheck_append' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedClassCheck_append

/--
info: 'QldpcVerification.SectorPackingCertificates.rawRep_range_of_mixedRangeCheck' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.rawRep_range_of_mixedRangeCheck

/--
info: 'QldpcVerification.SectorPackingCertificates.decodeMixed_base_no_wrap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.decodeMixed_base_no_wrap

/--
info: 'QldpcVerification.SectorPackingCertificates.decodeMixed_row_no_wrap' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.decodeMixed_row_no_wrap

/--
info: 'QldpcVerification.SectorPackingCertificates.mixed_mask_bound_of_rangeCheck' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixed_mask_bound_of_rangeCheck

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedPairCheck_append' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedPairCheck_append

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedPairCheck_parity' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedPairCheck_parity

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedClassCheck_map_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedClassCheck_map_sound

/--
info: 'QldpcVerification.SectorPackingCertificates.mixedPairCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.mixedPairCheck_sound

/--
info: 'QldpcVerification.SectorPackingCertificates.pattern_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QldpcVerification.SectorPackingCertificates.pattern_of_check

