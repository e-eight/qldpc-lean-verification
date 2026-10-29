import QldpcVerification.Overlap

/-! Finite paired-vector certificates discharge logical-class coverage for any k. -/

namespace QldpcVerification

open Matrix Module
open Quantum.Stabilizer.Homological

variable {Q : Type} [Fintype Q]

def pairingMap {k : ℕ} (z : Fin k → Q → ZMod 2) :
    (Q → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x j := x ⬝ᵥ z j
  map_add' x y := by ext j; exact add_dotProduct x y (z j)
  map_smul' a x := by ext j; exact smul_dotProduct a x (z j)

/-- A finite set of logical coordinates, certified by dual witnesses and a rank bound. -/
structure CoverageCertificate (S B : Submodule (ZMod 2) (Q → ZMod 2)) (k : ℕ) where
  boundary_le : B ≤ S
  detectors : Fin k → Q → ZMod 2
  witnesses : Fin k → Q → ZMod 2
  witness_mem : ∀ i, witnesses i ∈ S
  boundary_zero : ∀ b, b ∈ B → ∀ j, b ⬝ᵥ detectors j = 0
  paired : ∀ i j, witnesses i ⬝ᵥ detectors j = if i = j then 1 else 0
  dimension_bound : finrank (ZMod 2) S ≤ finrank (ZMod 2) B + k

namespace CoverageCertificate

variable {S B : Submodule (ZMod 2) (Q → ZMod 2)} {k : ℕ}
variable (C : CoverageCertificate S B k)

def coordinates : S →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  (pairingMap C.detectors).comp S.subtype

theorem coordinates_surjective : Function.Surjective C.coordinates := by
  classical
  intro a
  let u : Fin k → S := fun i => ⟨C.witnesses i, C.witness_mem i⟩
  refine ⟨∑ i, a i • u i, ?_⟩
  ext j
  change (pairingMap C.detectors) (↑(∑ i, a i • u i) : Q → ZMod 2) j = a j
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, a i * (C.witnesses i ⬝ᵥ C.detectors j)) = a j
  simp [C.paired]

theorem boundary_eq_kernel : B.comap S.subtype = LinearMap.ker C.coordinates := by
  have hle : B.comap S.subtype ≤ LinearMap.ker C.coordinates := by
    intro b hb
    change (pairingMap C.detectors) (b : Q → ZMod 2) = 0
    ext j
    exact C.boundary_zero b hb j
  have hb : finrank (ZMod 2) (B.comap S.subtype) = finrank (ZMod 2) B :=
    (Submodule.comapSubtypeEquivOfLe C.boundary_le).finrank_eq
  have hr := LinearMap.finrank_range_add_finrank_ker C.coordinates
  rw [LinearMap.range_eq_top.mpr C.coordinates_surjective, finrank_top,
    Module.finrank_fin_fun] at hr
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [hb]
  have hd := C.dimension_bound
  omega

theorem mem_boundary_iff {x : Q → ZMod 2} (hx : x ∈ S) :
    x ∈ B ↔ ∀ j, x ⬝ᵥ C.detectors j = 0 := by
  constructor
  · exact C.boundary_zero x
  · intro h
    have hk : (⟨x, hx⟩ : S) ∈ LinearMap.ker C.coordinates := by
      change (pairingMap C.detectors) x = 0
      ext j
      exact h j
    rw [← C.boundary_eq_kernel] at hk
    exact hk

theorem detects {x : Q → ZMod 2} (hx : x ∈ S) (hb : x ∉ B) :
    ∃ j, x ⬝ᵥ C.detectors j = 1 := by
  classical
  by_contra h
  apply hb
  apply (C.mem_boundary_iff hx).mpr
  intro j
  have hj : x ⬝ᵥ C.detectors j ≠ 1 := by simpa using not_exists.mp h j
  have ht : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact ht _ hj

theorem difference_mem_iff {x y : Q → ZMod 2} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ B ↔ ∀ j, x ⬝ᵥ C.detectors j = y ⬝ᵥ C.detectors j := by
  rw [C.mem_boundary_iff (S.sub_mem hx hy)]
  simp only [sub_dotProduct, sub_eq_zero]

include C in
theorem dimension_eq : finrank (ZMod 2) S = finrank (ZMod 2) B + k := by
  have hr := LinearMap.finrank_range_add_finrank_ker C.coordinates
  rw [LinearMap.range_eq_top.mpr C.coordinates_surjective, finrank_top,
    Module.finrank_fin_fun, ← C.boundary_eq_kernel] at hr
  have hb := (Submodule.comapSubtypeEquivOfLe C.boundary_le).finrank_eq
  omega

end CoverageCertificate

namespace Homological

open HomologicalCode

variable (X : HomologicalCode)

theorem dual_boundaries_le_dual_cycles : X.dualBoundaries ≤ X.dualCycles := by
  rintro c ⟨s, rfl⟩
  change X.dualBoundary (X.cutMap s) = 0
  ext f
  change (∑ e, X.cutMap s e * X.boundary2 (Pi.single f 1) e) = 0
  have h := X.boundary1_cutMap_transpose (X.boundary2 (Pi.single f 1)) s
  rw [X.boundary_comp_apply] at h
  simpa [mul_comm] using h.symm

theorem boundary_pairs_zero {b z : X.C1 → ZMod 2}
    (hb : b ∈ X.boundaries) (hz : z ∈ X.dualCycles) : b ⬝ᵥ z = 0 := by
  obtain ⟨f, rfl⟩ := hb
  have hz0 : X.dualBoundary z = 0 := hz
  change (∑ e, X.boundary2 f e * z e) = 0
  rw [X.boundary2_dualBoundary_transpose, hz0]
  simp

theorem dual_boundary_pairs_zero {b x : X.C1 → ZMod 2}
    (hb : b ∈ X.dualBoundaries) (hx : x ∈ X.cycles) : b ⬝ᵥ x = 0 := by
  obtain ⟨s, rfl⟩ := hb
  have hx0 : X.boundary1 x = 0 := hx
  rw [dotProduct_comm]
  have h := X.boundary1_cutMap_transpose x s
  rw [hx0] at h
  simpa using h.symm

/-- Coverage-certified X bound: the universal coverage premise is now discharged. -/
theorem chain_weight_ge_of_certificate {k : ℕ} {I : Type} [Fintype I]
    (C : CoverageCertificate X.cycles X.boundaries k)
    (reps : Fin k → I → X.C1 → ZMod 2) (w : Fin k → I → ℕ)
    (cap : Fin k → ℕ) (D : ℕ)
    (hclass : ∀ a i, reps a i - C.detectors a ∈ X.dualBoundaries)
    (hcap : ∀ a q, (∑ i, if reps a i q ≠ 0 then w a i else 0) ≤ cap a)
    (hthreshold : ∀ a, (D - 1) * cap a < ∑ i, w a i) :
    ∀ x, x ∈ X.cycles → x ∉ X.boundaries → D ≤ X.chainWeight x :=
  chain_weight_ge_of_detecting_families X C.detectors reps w cap D hclass
    (fun _ hx hb => C.detects hx hb) hcap hthreshold

theorem dual_chain_weight_ge_of_certificate {k : ℕ} {I : Type} [Fintype I]
    (C : CoverageCertificate X.dualCycles X.dualBoundaries k)
    (reps : Fin k → I → X.C1 → ZMod 2) (w : Fin k → I → ℕ)
    (cap : Fin k → ℕ) (D : ℕ)
    (hclass : ∀ a i, reps a i - C.detectors a ∈ X.boundaries)
    (hcap : ∀ a q, (∑ i, if reps a i q ≠ 0 then w a i else 0) ≤ cap a)
    (hthreshold : ∀ a, (D - 1) * cap a < ∑ i, w a i) :
    ∀ x, x ∈ X.dualCycles → x ∉ X.dualBoundaries → D ≤ X.chainWeight x :=
  dual_chain_weight_ge_of_detecting_families X C.detectors reps w cap D hclass
    (fun _ hx hb => C.detects hx hb) hcap hthreshold

end Homological
end QldpcVerification
