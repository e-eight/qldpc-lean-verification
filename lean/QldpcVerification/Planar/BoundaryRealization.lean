import QldpcVerification.Planar.BoundaryPolynomial
import QldpcVerification.Planar.BoundaryCharge

/-! From a physical full-syndrome kernel to complete boundary charges.
The numerical dimensions are those of the explicit rectangle; concrete matrix
and polynomial identifications must still be supplied by an application. -/

namespace QldpcVerification.Planar.BoundaryRealization

open Module

abbrev F := ZMod 2
abbrev A := ChargeAlgebra.A
abbrev Poly := BulkExactness.Bivariate
abbrev E := BoundaryResidue.Boundary

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

noncomputable def boundaryMap (σ : V →ₗ[F] Poly) (S : Submodule F V) :
    S →ₗ[F] E := BoundaryPolynomial.extract.comp (σ.comp S.subtype)

theorem boundaryMap_kernel (σ : V →ₗ[F] Poly) (S : Submodule F V)
    (hsquare : ∀ v, BulkExactness.InSquare 20 (σ v))
    (hgap : ∀ v ∈ S, ∀ i, 2 ≤ i → i ≤ 18 → (σ v).coeff i = 0) :
    LinearMap.ker (boundaryMap σ S) = (LinearMap.ker σ).comap S.subtype := by
  ext v
  change BoundaryPolynomial.extract (σ v.val) = 0 ↔ σ v.val = 0
  constructor
  · intro hv
    have he := BoundaryPolynomial.encode_extract (σ v.val) (hsquare v.val)
      (hgap v.val v.property)
    rw [hv, map_zero] at he
    exact he.symm
  · intro hv
    rw [hv, map_zero]

theorem boundaryMap_range_finrank (σ : V →ₗ[F] Poly) (S : Submodule F V)
    (hS : finrank F S = 365)
    (hker : finrank F (LinearMap.ker σ) = 289)
    (hkerle : LinearMap.ker σ ≤ S)
    (hsquare : ∀ v, BulkExactness.InSquare 20 (σ v))
    (hgap : ∀ v ∈ S, ∀ i, 2 ≤ i → i ≤ 18 → (σ v).coeff i = 0) :
    finrank F (LinearMap.range (boundaryMap σ S)) = 76 := by
  have hk : finrank F (LinearMap.ker (boundaryMap σ S)) = 289 := by
    rw [boundaryMap_kernel σ S hsquare hgap]
    exact (Submodule.comapSubtypeEquivOfLe hkerle).finrank_eq.trans hker
  have hr := LinearMap.finrank_range_add_finrank_ker (boundaryMap σ S)
  rw [hk, hS] at hr
  omega

/-- Completeness requires actual syndrome, support, and stabilizer hypotheses;
no dimension-only identification is assumed. -/
theorem complete (σ : V →ₗ[F] Poly) (S : Submodule F V) (B : Submodule F S)
    (total left : E →ₗ[F] A)
    (hS : finrank F S = 365) (hB : finrank F B = 357)
    (hker : finrank F (LinearMap.ker σ) = 289)
    (hkerle : LinearMap.ker σ ≤ S)
    (hsquare : ∀ v, BulkExactness.InSquare 20 (σ v))
    (hgap : ∀ v ∈ S, ∀ i, 2 ≤ i → i ≤ 18 → (σ v).coeff i = 0)
    (htotal : ∀ v ∈ S, total (BoundaryPolynomial.extract (σ v)) = 0)
    (hTotalRank : finrank F (LinearMap.ker total) = 76)
    (hlift : ∀ a, ∃ e, total e = 0 ∧ left e = a)
    (hzero : ∀ b ∈ B, left (boundaryMap σ S b) = 0) :
    Function.Surjective (left.comp (boundaryMap σ S)) ∧
      B = LinearMap.ker (left.comp (boundaryMap σ S)) := by
  have hle : LinearMap.range (boundaryMap σ S) ≤ LinearMap.ker total := by
    rintro _ ⟨v, rfl⟩
    exact htotal v.val v.property
  have hr := boundaryMap_range_finrank σ S hS hker hkerle hsquare hgap
  have himage : LinearMap.range (boundaryMap σ S) = LinearMap.ker total := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hr, hTotalRank]
  have honto := BoundaryCharge.charge_surjective (boundaryMap σ S) total left himage hlift
  refine ⟨honto, BoundaryCharge.boundary_eq_kernel B _ hzero honto ?_⟩
  rw [hS, hB, ChargeAlgebra.finrank_eq_eight]

end QldpcVerification.Planar.BoundaryRealization
