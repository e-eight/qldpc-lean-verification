import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Dimension-based completeness of a boundary-charge map.
These abstract lemmas do not assert any concrete 722-code application. -/

namespace QldpcVerification.Planar.BoundaryCharge

open Module

variable {F V E K : Type*} [Field F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup E] [Module F E] [FiniteDimensional F E]
  [AddCommGroup K] [Module F K] [FiniteDimensional F K]

theorem range_eq_kernel (syndrome : V →ₗ[F] E) (total : E →ₗ[F] K)
    (hzero : ∀ v, total (syndrome v) = 0)
    (honto : Function.Surjective total)
    (hdim : finrank F (LinearMap.range syndrome) + finrank F K = finrank F E) :
    LinearMap.range syndrome = LinearMap.ker total := by
  have hle : LinearMap.range syndrome ≤ LinearMap.ker total := by
    rintro _ ⟨v, rfl⟩
    exact hzero v
  have hr := LinearMap.finrank_range_add_finrank_ker total
  rw [LinearMap.range_eq_top.mpr honto, finrank_top] at hr
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

theorem charge_surjective (syndrome : V →ₗ[F] E) (total left : E →ₗ[F] K)
    (himage : LinearMap.range syndrome = LinearMap.ker total)
    (hlift : ∀ k, ∃ e, total e = 0 ∧ left e = k) :
    Function.Surjective (left.comp syndrome) := by
  intro k
  obtain ⟨e, he, hk⟩ := hlift k
  have hm : e ∈ LinearMap.range syndrome := by
    rw [himage]
    exact he
  obtain ⟨v, hv⟩ := hm
  refine ⟨v, ?_⟩
  simpa only [LinearMap.comp_apply, hv] using hk

theorem boundary_eq_kernel (B : Submodule F V) (charge : V →ₗ[F] K)
    (hzero : ∀ b ∈ B, charge b = 0)
    (honto : Function.Surjective charge)
    (hdim : finrank F V ≤ finrank F B + finrank F K) :
    B = LinearMap.ker charge := by
  have hle : B ≤ LinearMap.ker charge := hzero
  have hr := LinearMap.finrank_range_add_finrank_ker charge
  rw [LinearMap.range_eq_top.mpr honto, finrank_top] at hr
  apply Submodule.eq_of_le_of_finrank_le hle
  omega

theorem detects (B : Submodule F V) (charge : V →ₗ[F] K)
    (hkernel : B = LinearMap.ker charge) (v : V) (hv : v ∉ B) : charge v ≠ 0 := by
  intro h
  apply hv
  rw [hkernel]
  exact h

section Split

variable {L R : Type*} [AddCommGroup L] [Module F L]
  [AddCommGroup R] [Module F R]

theorem split_lift (low : L →ₗ[F] K) (high : R →ₗ[F] K)
    (hlow : Function.Surjective low) (hhigh : Function.Surjective high) (k : K) :
    ∃ p : L × R, low p.1 + high p.2 = 0 ∧ low p.1 = k := by
  obtain ⟨l, hl⟩ := hlow k
  obtain ⟨r, hr⟩ := hhigh (-k)
  exact ⟨(l, r), by simp [hl, hr], hl⟩

end Split
end QldpcVerification.Planar.BoundaryCharge
