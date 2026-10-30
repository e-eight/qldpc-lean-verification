import QldpcVerification.Input.Homological
import QldpcVerification.Input.SparseCertificates
import QldpcVerification.Lattice.IncidenceRank
import QldpcVerification.Lattice.Winding

/-! A construction-level regression for GB(1+x,1+x^3,8), with parameters
[[16,2,4]]. This is not the challenge's separately indexed 16-2-4 JSON.
The cyclic length is even. Raw block parities miss a nontrivial logical,
while period-aware winding coordinates detect every logical class.
-/

namespace QldpcVerification.EvenBicycle16

open Matrix Module Input Input.Sparse Lattice
open Quantum.Stabilizer.Homological

def blockEquiv : (ZMod 8 ⊕ ZMod 8) ≃ Fin 16 := finSumFinEquiv

def horizontal (q : Fin 16) : Bool :=
  match blockEquiv.symm q with
  | .inl _ => true
  | .inr _ => false

def source (q : Fin 16) : ZMod 8 :=
  match blockEquiv.symm q with
  | .inl v => v
  | .inr v => v

def xTarget (q : Fin 16) : ZMod 8 := source q + if horizontal q then 1 else 3
def zTarget (q : Fin 16) : ZMod 8 := source q - if horizontal q then 3 else 1

def code : CSSCode 16 8 8 where
  HX i q := incidence source xTarget q i
  HZ i q := incidence source zTarget q i
  comm := by decide +kernel

theorem x_step (q : Fin 16) : xTarget q - source q = if horizontal q then 1 else 3 := by
  simp [xTarget]

theorem z_step (q : Fin 16) : zTarget q - source q = if horizontal q then -3 else -1 := by
  cases h : horizontal q <;> simp [zTarget, h]

def xLift : WindingData source xTarget horizontal :=
  cyclicWindingData source xTarget horizontal 1 3 x_step

def zLift : WindingData source zTarget horizontal :=
  cyclicWindingData source zTarget horizontal (-3) (-1) (by simpa using z_step)

def xDetector (i : Fin 2) (q : Fin 16) : ZMod 2 :=
  if i = 0 then (zLift.label q).1 else (zLift.label q).2

def zDetector (i : Fin 2) (q : Fin 16) : ZMod 2 :=
  if i = 0 then (xLift.label q).1 else (xLift.label q).2

def xWitness (i : Fin 2) : Vec 16 := vec 16 (if i = 0 then 255 else 49409)
def zWitness (i : Fin 2) : Vec 16 := vec 16 (if i = 0 then 255 else 263)

theorem x_witness_kernel : ∀ i, code.HZ.mulVec (xWitness i) = 0 := by decide +kernel
theorem z_witness_kernel : ∀ i, code.HX.mulVec (zWitness i) = 0 := by decide +kernel
theorem x_detector_kernel : ∀ i, code.HX.mulVec (xDetector i) = 0 := by decide +kernel
theorem z_detector_kernel : ∀ i, code.HZ.mulVec (zDetector i) = 0 := by decide +kernel
theorem x_paired : ∀ i j, xWitness i ⬝ᵥ xDetector j = if i = j then 1 else 0 := by
  decide +kernel
theorem z_paired : ∀ i j, zWitness i ⬝ᵥ zDetector j = if i = j then 1 else 0 := by
  decide +kernel

theorem x_connected (f : ZMod 8 → ZMod 2)
    (h : ∀ q, f (source q) = f (xTarget q)) : ∀ v, f v = f 0 := by
  intro v
  apply constant_of_periodic f 1 1 (by decide) (fun w => ?_) v
  simpa [source, xTarget, horizontal] using (h (blockEquiv (.inl w))).symm

theorem z_connected (f : ZMod 8 → ZMod 2)
    (h : ∀ q, f (source q) = f (zTarget q)) : ∀ v, f v = f 0 := by
  intro v
  apply constant_of_periodic f (-1) (-1) (by decide) (fun w => ?_) v
  simpa [source, zTarget, horizontal, sub_eq_add_neg] using (h (blockEquiv (.inr w))).symm

theorem rankX_lower : 7 ≤ finrank (ZMod 2) code.xStab :=
  incidence_rank_lower source xTarget 0 code.HX (fun _ _ => rfl) x_connected

theorem rankZ_lower : 7 ≤ finrank (ZMod 2) code.zStab :=
  incidence_rank_lower source zTarget 0 code.HZ (fun _ _ => rfl) z_connected

theorem rank_sum_bound : 16 ≤ finrank (ZMod 2) code.xStab + finrank (ZMod 2) code.zStab + 2 := by
  have hx := rankX_lower
  have hz := rankZ_lower
  omega

def xCoverage : CoverageCertificate code.homological.cycles code.homological.boundaries 2 where
  boundary_le := code.homological.boundaries_le_cycles
  detectors := xDetector
  witnesses := xWitness
  witness_mem := x_witness_kernel
  boundary_zero := fun _ hb j => Homological.boundary_pairs_zero _ hb (by
    change code.homological.dualBoundary (xDetector j) = 0
    rw [code.dualBoundary_eq]
    exact x_detector_kernel j)
  paired := x_paired
  dimension_bound := code.dimension_bound rank_sum_bound

def zCoverage : CoverageCertificate code.homological.dualCycles code.homological.dualBoundaries 2 where
  boundary_le := Homological.dual_boundaries_le_dual_cycles _
  detectors := zDetector
  witnesses := zWitness
  witness_mem := fun j => by
    change code.homological.dualBoundary (zWitness j) = 0
    rw [code.dualBoundary_eq]
    exact z_witness_kernel j
  boundary_zero := fun _ hb j => Homological.dual_boundary_pairs_zero _ hb (z_detector_kernel j)
  paired := z_paired
  dimension_bound := code.dual_dimension_bound rank_sum_bound

theorem encoded_qubits : 16 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2 := by
  have hd := xCoverage.dimension_eq
  rw [code.boundaries_eq] at hd
  have hr := Input.CSSCode.rank_nullity code.HZ
  change finrank (ZMod 2) (LinearMap.ker code.HZ.mulVecLin) =
    finrank (ZMod 2) code.xStab + 2 at hd
  change finrank (ZMod 2) (LinearMap.ker code.HZ.mulVecLin) +
    finrank (ZMod 2) code.zStab = 16 at hr
  omega

theorem ranks : finrank (ZMod 2) code.xStab = 7 ∧ finrank (ZMod 2) code.zStab = 7 := by
  have hx := rankX_lower
  have hz := rankZ_lower
  have hk := encoded_qubits
  omega

theorem x_closed_zero_boundary {v : ZMod 8} (p : Walk source zTarget v v)
    (hz : p.displacement horizontal = 0) : p.binaryChain ∈ code.xStab := by
  rw [← code.boundaries_eq]
  exact zero_displacement_boundary source zTarget horizontal xCoverage zLift
    (by intro q; simp [xCoverage, xDetector]) p
    (p.closed_chain_kernel code.HZ (fun _ _ => rfl)) hz

theorem z_closed_zero_boundary {v : ZMod 8} (p : Walk source xTarget v v)
    (hz : p.displacement horizontal = 0) : p.binaryChain ∈ code.zStab := by
  rw [← code.dualBoundaries_eq]
  apply zero_displacement_boundary source xTarget horizontal zCoverage xLift
    (by intro q; simp [zCoverage, zDetector]) p ?_ hz
  change code.homological.dualBoundary p.binaryChain = 0
  rw [code.dualBoundary_eq]
  exact p.closed_chain_kernel code.HX (fun _ _ => rfl)

theorem lattice_finite : ∀ i j : Fin 7,
    let u : ℤ := i.val - 3
    let v : ℤ := j.val - 3
    u.natAbs + v.natAbs ≤ 3 → (u + 3 * v) % 8 = 0 → u = 0 ∧ v = 0 := by
  decide +kernel

theorem lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod 8) * (u : ZMod 8) + 3 * (v : ZMod 8) = 0) :
    4 ≤ u.natAbs + v.natAbs := by
  by_contra h
  have hs : u.natAbs + v.natAbs ≤ 3 := by omega
  let i : Fin 7 := ⟨(u + 3).toNat, by omega⟩
  let j : Fin 7 := ⟨(v + 3).toNat, by omega⟩
  have hi : (i.val : ℤ) - 3 = u := by dsimp [i]; omega
  have hj : (j.val : ℤ) - 3 = v := by dsimp [j]; omega
  have he : (u + 3 * v) % 8 = 0 := by
    apply Int.emod_eq_zero_of_dvd
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa using hc
  have hh := lattice_finite i j
  dsimp only at hh
  rw [hi, hj] at hh
  obtain ⟨rfl, rfl⟩ := hh hs he
  simp at hn

theorem dual_lattice_bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (-3 : ZMod 8) * (u : ZMod 8) + -1 * (v : ZMod 8) = 0) :
    4 ≤ u.natAbs + v.natAbs := by
  have h : (1 : ZMod 8) * ((-v : ℤ) : ZMod 8) + 3 * ((-u : ℤ) : ZMod 8) = 0 := by
    push_cast
    linear_combination hc
  have hh := lattice_bound (-v) (-u) (by simpa using hn.symm) h
  simpa [Nat.add_comm] using hh

theorem x_lower (x : Vec 16) (hx : code.IsXLogical x) : 4 ≤ hammingNorm x := by
  obtain ⟨hc, hb⟩ := (code.x_logical_iff x).mp hx
  exact weight_ge_of_coordinate_certificate horizontal xCoverage (-3 : ZMod 8) (-1)
    source zTarget z_step zLift.label (fun _ => zLift.closed_zero)
    (by intro q; simp [xCoverage, xDetector])
    (fun x hx => cycle_of_kernel source zTarget code.HZ (fun _ _ => rfl) x hx)
    4 dual_lattice_bound x hc hb

theorem z_lower (z : Vec 16) (hz : code.IsZLogical z) : 4 ≤ hammingNorm z := by
  obtain ⟨hc, hb⟩ := (code.z_logical_iff z).mp hz
  exact weight_ge_of_coordinate_certificate horizontal zCoverage (1 : ZMod 8) 3
    source xTarget x_step xLift.label (fun _ => xLift.closed_zero)
    (by intro q; simp [zCoverage, zDetector])
    (fun z hz => cycle_of_kernel source xTarget code.HX (fun _ _ => rfl) z (by
      change code.homological.dualBoundary z = 0 at hz
      rwa [code.dualBoundary_eq] at hz))
    4 lattice_bound z hc hb

theorem x_witness_logical (i : Fin 2) : code.IsXLogical (xWitness i) := by
  rw [code.x_logical_iff]
  refine ⟨xCoverage.witness_mem i, ?_⟩
  intro hb
  have h := xCoverage.boundary_zero _ hb i
  have hp : xWitness i ⬝ᵥ xCoverage.detectors i = 1 := by simpa using xCoverage.paired i i
  exact one_ne_zero (hp.symm.trans h)

theorem z_witness_logical (i : Fin 2) : code.IsZLogical (zWitness i) := by
  rw [code.z_logical_iff]
  refine ⟨zCoverage.witness_mem i, ?_⟩
  intro hb
  have h := zCoverage.boundary_zero _ hb i
  have hp : zWitness i ⬝ᵥ zCoverage.detectors i = 1 := by simpa using zCoverage.paired i i
  exact one_ne_zero (hp.symm.trans h)

theorem distX : code.DistX 4 :=
  ⟨⟨xWitness 1, x_witness_logical 1, by decide +kernel⟩, x_lower⟩

theorem distZ : code.DistZ 4 :=
  ⟨⟨zWitness 1, z_witness_logical 1, by decide +kernel⟩, z_lower⟩

theorem parameters :
    (16 - finrank (ZMod 2) code.xStab - finrank (ZMod 2) code.zStab = 2) ∧
      code.DistX 4 ∧ code.DistZ 4 := ⟨encoded_qubits, distX, distZ⟩

def rawDetector (i : Fin 2) (q : Fin 16) : ZMod 2 :=
  if i = 0 then (axisLabel horizontal q).1 else (axisLabel horizontal q).2

theorem raw_parity_misses_logical :
    code.IsXLogical (xWitness 0) ∧
      (∀ i, xWitness 0 ⬝ᵥ rawDetector i = 0) ∧ xWitness 0 ⬝ᵥ xDetector 0 = 1 := by
  refine ⟨x_witness_logical 0, ?_, ?_⟩
  · decide +kernel
  · exact x_paired 0 0

end QldpcVerification.EvenBicycle16
