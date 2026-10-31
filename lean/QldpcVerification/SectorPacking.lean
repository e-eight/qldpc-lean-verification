import QldpcVerification.Coverage

/-!
Packings conditioned on complete logical coordinates. Representatives may have
different logical classes: each must annihilate the boundary space and pair to
one with the chosen reference. No change of physical coordinates is involved.
-/

namespace QldpcVerification.SectorPacking

open Matrix Finset
open Quantum.Stabilizer.Homological

variable {Q I : Type} [Fintype Q] [Fintype I]
variable {S B : Submodule (ZMod 2) (Q → ZMod 2)} {k : ℕ}

/-- Equal complete coordinates transfer pairings with any boundary annihilator. -/
theorem pairing_eq_of_coordinates (C : CoverageCertificate S B k)
    {x r z : Q → ZMod 2} (hx : x ∈ S) (hr : r ∈ S)
    (hcoordinates : C.coordinates ⟨x, hx⟩ = C.coordinates ⟨r, hr⟩)
    (hboundary : ∀ b, b ∈ B → b ⬝ᵥ z = 0) : x ⬝ᵥ z = r ⬝ᵥ z := by
  have hdifference : x - r ∈ B := (C.difference_mem_iff hx hr).mpr
    (fun j => congrFun hcoordinates j)
  have hzero := hboundary (x - r) hdifference
  rw [sub_dotProduct] at hzero
  exact sub_eq_zero.mp hzero

/-- A finite natural-weight packing bounds every cycle in the reference sector. -/
theorem weight_ge_of_sector (C : CoverageCertificate S B k)
    (r : Q → ZMod 2) (hr : r ∈ S) (z : I → Q → ZMod 2)
    (w : I → ℕ) (cap D : ℕ)
    (hboundary : ∀ i b, b ∈ B → b ⬝ᵥ z i = 0)
    (hpair : ∀ i, r ⬝ᵥ z i = 1)
    (hcap : ∀ q, (∑ i, if z i q ≠ 0 then w i else 0) ≤ cap)
    (hthreshold : (D - 1) * cap < ∑ i, w i)
    {x : Q → ZMod 2} (hx : x ∈ S)
    (hcoordinates : C.coordinates ⟨x, hx⟩ = C.coordinates ⟨r, hr⟩) :
    D ≤ hammingNorm x := by
  have hpairs : ∀ i, x ⬝ᵥ z i = 1 := fun i =>
    (pairing_eq_of_coordinates C hx hr hcoordinates (hboundary i)).trans (hpair i)
  have hcount := weighted_overlap_bound x z w cap hpairs hcap
  by_contra h
  have hw : hammingNorm x ≤ D - 1 := by omega
  have hh := Nat.mul_le_mul_left cap hw
  nlinarith

/-- Finite data for one coordinate pattern; annihilation is an explicit field. -/
structure Certificate (C : CoverageCertificate S B k) (c : Fin k → ZMod 2)
    (D : ℕ) where
  size : ℕ
  reference : S
  reference_coordinates : C.coordinates reference = c
  representatives : Fin size → Q → ZMod 2
  weights : Fin size → ℕ
  cap : ℕ
  boundary_zero : ∀ i b, b ∈ B → b ⬝ᵥ representatives i = 0
  pairs_one : ∀ i, (reference : Q → ZMod 2) ⬝ᵥ representatives i = 1
  capacity : ∀ q, (∑ i, if representatives i q ≠ 0 then weights i else 0) ≤ cap
  threshold : (D - 1) * cap < ∑ i, weights i

namespace Certificate

theorem lower_bound {C : CoverageCertificate S B k} {c : Fin k → ZMod 2} {D : ℕ}
    (P : Certificate C c D) {x : Q → ZMod 2} (hx : x ∈ S)
    (hcoordinates : C.coordinates ⟨x, hx⟩ = c) : D ≤ hammingNorm x :=
  weight_ge_of_sector C P.reference P.reference.property P.representatives P.weights
    P.cap D P.boundary_zero P.pairs_one P.capacity P.threshold hx
    (hcoordinates.trans P.reference_coordinates.symm)

end Certificate

/-- Coordinates of a nontrivial cycle cannot all vanish. -/
theorem coordinates_ne_zero (C : CoverageCertificate S B k)
    {x : Q → ZMod 2} (hx : x ∈ S) (hb : x ∉ B) :
    C.coordinates ⟨x, hx⟩ ≠ 0 := by
  intro hzero
  obtain ⟨j, hj⟩ := C.detects hx hb
  have hz : x ⬝ᵥ C.detectors j = 0 := congrFun hzero j
  rw [hj] at hz
  exact one_ne_zero hz

/-- Assemble known detector bounds with certificates covering every residual pattern.
The coverage predicate concerns all nonzero coordinates, not merely basis vectors. -/
theorem weight_ge_of_coordinate_cover (C : CoverageCertificate S B k)
    (D : ℕ) (good : Fin k → Prop) (residual : (Fin k → ZMod 2) → Prop)
    (hcover : ∀ c, c ≠ 0 → (∃ j, good j ∧ c j = 1) ∨ residual c)
    (hgood : ∀ x (hx : x ∈ S), x ∉ B → ∀ j, good j →
      C.coordinates ⟨x, hx⟩ j = 1 → D ≤ hammingNorm x)
    (hresidual : ∀ c, residual c → Certificate C c D) :
    ∀ x, x ∈ S → x ∉ B → D ≤ hammingNorm x := by
  intro x hx hb
  rcases hcover _ (coordinates_ne_zero C hx hb) with ⟨j, hj, hpair⟩ | hrest
  · exact hgood x hx hb j hj hpair
  · exact (hresidual _ hrest).lower_bound hx rfl

variable {r s : ℕ}

/-- A residual coordinate vector with a zero prefix. This is not a physical map. -/
def residualCoordinates (tail : Fin s → ZMod 2) : Fin (r + s) → ZMod 2 :=
  Fin.addCases (fun _ => 0) tail

/-- The exact number of residual proof obligations. No enumeration is required. -/
theorem residual_pattern_count (s : ℕ) :
    Fintype.card {tail : Fin s → ZMod 2 // tail ≠ 0} = 2 ^ s - 1 := by
  simp

theorem eq_residualCoordinates (c : Fin (r + s) → ZMod 2)
    (hprefix : ∀ i : Fin r, c (Fin.castAdd s i) = 0) :
    c = residualCoordinates (r := r) (fun j => c (Fin.natAdd r j)) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa [residualCoordinates] using hprefix i
  · simp [residualCoordinates]

theorem suffix_ne_zero (c : Fin (r + s) → ZMod 2) (hne : c ≠ 0)
    (hprefix : ∀ i : Fin r, c (Fin.castAdd s i) = 0) :
    (fun j : Fin s => c (Fin.natAdd r j)) ≠ 0 := by
  intro htail
  apply hne
  rw [eq_residualCoordinates c hprefix, htail]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [residualCoordinates]

/-- A prefix hit, or a nonzero suffix. All nonzero suffixes remain obligations. -/
theorem prefix_or_residual (c : Fin (r + s) → ZMod 2) (hne : c ≠ 0) :
    (∃ i : Fin r, c (Fin.castAdd s i) = 1) ∨
      ∃ tail : Fin s → ZMod 2, tail ≠ 0 ∧ c = residualCoordinates (r := r) tail := by
  classical
  by_cases h : ∃ i : Fin r, c (Fin.castAdd s i) = 1
  · exact Or.inl h
  · right
    have hprefix : ∀ i : Fin r, c (Fin.castAdd s i) = 0 := by
      intro i
      have hi : c (Fin.castAdd s i) ≠ 1 := fun hi => h ⟨i, hi⟩
      have hbit : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
      exact hbit _ hi
    exact ⟨_, suffix_ne_zero c hne hprefix, eq_residualCoordinates c hprefix⟩

/-- With a full paired `r+s` basis, only the `2^s-1` nonzero suffixes need
sector certificates once each of the first `r` detectors has a global bound. -/
theorem weight_ge_of_prefix_sectors (C : CoverageCertificate S B (r + s))
    (D : ℕ)
    (hgood : ∀ x (hx : x ∈ S), x ∉ B → ∀ j : Fin r,
      C.coordinates ⟨x, hx⟩ (Fin.castAdd s j) = 1 → D ≤ hammingNorm x)
    (hsectors : ∀ tail : Fin s → ZMod 2, tail ≠ 0 →
      Certificate C (residualCoordinates (r := r) tail) D) :
    ∀ x, x ∈ S → x ∉ B → D ≤ hammingNorm x := by
  intro x hx hb
  rcases prefix_or_residual (C.coordinates ⟨x, hx⟩)
      (coordinates_ne_zero C hx hb) with ⟨j, hj⟩ | ⟨tail, htail, hc⟩
  · exact hgood x hx hb j hj
  · exact (hsectors tail htail).lower_bound hx hc

namespace Homological

variable (X : HomologicalCode) {k : ℕ} {I : Type} [Fintype I]

/-- X-sector specialization: opposite cycles annihilate X boundaries. -/
theorem chain_weight_ge_of_sector
    (C : CoverageCertificate X.cycles X.boundaries k)
    (r : X.C1 → ZMod 2) (hr : r ∈ X.cycles)
    (z : I → X.C1 → ZMod 2) (w : I → ℕ) (cap D : ℕ)
    (hz : ∀ i, z i ∈ X.dualCycles) (hpair : ∀ i, r ⬝ᵥ z i = 1)
    (hcap : ∀ q, (∑ i, if z i q ≠ 0 then w i else 0) ≤ cap)
    (hthreshold : (D - 1) * cap < ∑ i, w i)
    {x : X.C1 → ZMod 2} (hx : x ∈ X.cycles)
    (hc : C.coordinates ⟨x, hx⟩ = C.coordinates ⟨r, hr⟩) :
    D ≤ X.chainWeight x :=
  weight_ge_of_sector C r hr z w cap D
    (fun i _ hb => QldpcVerification.Homological.boundary_pairs_zero X hb (hz i))
    hpair hcap hthreshold hx hc

/-- Z-sector specialization, with the symmetric boundary annihilation condition. -/
theorem dual_chain_weight_ge_of_sector
    (C : CoverageCertificate X.dualCycles X.dualBoundaries k)
    (r : X.C1 → ZMod 2) (hr : r ∈ X.dualCycles)
    (z : I → X.C1 → ZMod 2) (w : I → ℕ) (cap D : ℕ)
    (hz : ∀ i, z i ∈ X.cycles) (hpair : ∀ i, r ⬝ᵥ z i = 1)
    (hcap : ∀ q, (∑ i, if z i q ≠ 0 then w i else 0) ≤ cap)
    (hthreshold : (D - 1) * cap < ∑ i, w i)
    {x : X.C1 → ZMod 2} (hx : x ∈ X.dualCycles)
    (hc : C.coordinates ⟨x, hx⟩ = C.coordinates ⟨r, hr⟩) :
    D ≤ X.chainWeight x :=
  weight_ge_of_sector C r hr z w cap D
    (fun i _ hb => QldpcVerification.Homological.dual_boundary_pairs_zero X hb (hz i))
    hpair hcap hthreshold hx hc

end Homological
end QldpcVerification.SectorPacking
