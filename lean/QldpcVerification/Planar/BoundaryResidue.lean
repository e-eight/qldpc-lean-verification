import QldpcVerification.Planar.ChargeAlgebra
import QldpcVerification.Planar.BoundaryCharge
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Prod

/-! Concrete actual722 boundary residue coordinates.

Each side consists of two rows of length 21. The two sides form an
84-dimensional space. These maps describe residue coordinates only; identifying
them with the physical syndrome requires the separate syndrome bridge.
-/

namespace QldpcVerification.Planar.BoundaryResidue

open Module ChargeAlgebra

noncomputable section

abbrev Row := Fin 21 → F
abbrev Side := Row × Row
abbrev Boundary := Side × Side

theorem row_finrank : finrank F Row = 21 := by
  simp [Row, Module.finrank_pi]

theorem side_finrank : finrank F Side = 42 := by
  simp [Side, Module.finrank_prod, row_finrank]

theorem boundary_finrank : finrank F Boundary = 84 := by
  simp [Boundary, Module.finrank_prod, side_finrank]

/-- Evaluate one row at the chosen charge coordinate. -/
def rowEval (z : A) : Row →ₗ[F] A where
  toFun c := ∑ j, c j • z ^ (j : ℕ)
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem rowEval_apply (z : A) (c : Row) :
    rowEval z c = ∑ j, c j • z ^ (j : ℕ) := rfl

/-- Put eight coefficients at indices 0 through 7; the last thirteen are zero. -/
def pad8 (c : Fin 8 → F) : Row := Fin.append c (fun _ : Fin 13 => 0)

@[simp] theorem rowEval_pad8 (z : A) (c : Fin 8 → F) :
    rowEval z (pad8 c) = ∑ i : Fin 8, c i • z ^ (i : ℕ) := by
  change (∑ j : Fin (8 + 13), Fin.append c (fun _ : Fin 13 => 0) j • z ^ (j : ℕ)) = _
  rw [Fin.sum_univ_add (a := 8) (b := 13)]
  simp

/-- X low-side residue: evaluate the two columns, with offsets 1 and x. -/
def lowX : Side →ₗ[F] A :=
  (rowEval y).coprod ((LinearMap.mulLeft F x).comp (rowEval y))

/-- Reflected-Z low-side residue: interchange the coordinate roles. -/
def lowZ : Side →ₗ[F] A :=
  (rowEval x).coprod ((LinearMap.mulLeft F y).comp (rowEval x))

def highX : Side →ₗ[F] A := (LinearMap.mulLeft F (x ^ 19)).comp lowX

def highZ : Side →ₗ[F] A := (LinearMap.mulLeft F (y ^ 19)).comp lowZ

@[simp] theorem lowX_apply (s : Side) :
    lowX s = (∑ j, s.1 j • y ^ (j : ℕ)) + x * (∑ j, s.2 j • y ^ (j : ℕ)) := rfl

@[simp] theorem lowZ_apply (s : Side) :
    lowZ s = (∑ j, s.1 j • x ^ (j : ℕ)) + y * (∑ j, s.2 j • x ^ (j : ℕ)) := rfl

@[simp] theorem highX_apply (s : Side) : highX s = x ^ 19 * lowX s := rfl

@[simp] theorem highZ_apply (s : Side) : highZ s = y ^ 19 * lowZ s := rfl

theorem lowX_surjective : Function.Surjective lowX := by
  intro a
  obtain ⟨c, hc⟩ := y_coordinates_surjective a
  refine ⟨(pad8 c, 0), ?_⟩
  change rowEval y (pad8 c) + x * rowEval y 0 = a
  rw [rowEval_pad8, map_zero, mul_zero, add_zero]
  exact hc

theorem lowZ_surjective : Function.Surjective lowZ := by
  intro a
  obtain ⟨c, hc⟩ := x_coordinates_surjective a
  refine ⟨(pad8 c, 0), ?_⟩
  change rowEval x (pad8 c) + y * rowEval x 0 = a
  rw [rowEval_pad8, map_zero, mul_zero, add_zero]
  exact hc

private theorem shifted_surjective (u : Aˣ) (L : Side →ₗ[F] A)
    (hL : Function.Surjective L) :
    Function.Surjective ((LinearMap.mulLeft F (u : A)).comp L) := by
  intro a
  obtain ⟨b, hb⟩ := (Units.mulLeftLinearEquiv F A u).surjective a
  obtain ⟨s, hs⟩ := hL b
  refine ⟨s, ?_⟩
  change (u : A) * L s = a
  rw [hs]
  exact hb

theorem highX_surjective : Function.Surjective highX := by
  simpa only [Units.val_pow_eq_pow_val] using shifted_surjective (xUnit ^ 19) lowX lowX_surjective

theorem highZ_surjective : Function.Surjective highZ := by
  simpa only [Units.val_pow_eq_pow_val] using shifted_surjective (yUnit ^ 19) lowZ lowZ_surjective

def totalX : Boundary →ₗ[F] A := lowX.coprod highX

def totalZ : Boundary →ₗ[F] A := lowZ.coprod highZ

def leftX : Boundary →ₗ[F] A := lowX.comp (LinearMap.fst F Side Side)

def leftZ : Boundary →ₗ[F] A := lowZ.comp (LinearMap.fst F Side Side)

@[simp] theorem totalX_apply (b : Boundary) : totalX b = lowX b.1 + highX b.2 := rfl

@[simp] theorem totalZ_apply (b : Boundary) : totalZ b = lowZ b.1 + highZ b.2 := rfl

@[simp] theorem leftX_apply (b : Boundary) : leftX b = lowX b.1 := rfl

@[simp] theorem leftZ_apply (b : Boundary) : leftZ b = lowZ b.1 := rfl

theorem totalX_surjective : Function.Surjective totalX := by
  intro a
  obtain ⟨s, hs⟩ := lowX_surjective a
  exact ⟨(s, 0), by simpa only [totalX_apply, map_zero, add_zero] using hs⟩

theorem totalZ_surjective : Function.Surjective totalZ := by
  intro a
  obtain ⟨s, hs⟩ := lowZ_surjective a
  exact ⟨(s, 0), by simpa only [totalZ_apply, map_zero, add_zero] using hs⟩

private theorem kernel_finrank (T : Boundary →ₗ[F] A) (hT : Function.Surjective T) :
    finrank F (LinearMap.ker T) = 76 := by
  have h := LinearMap.finrank_range_add_finrank_ker T
  rw [LinearMap.range_eq_top.mpr hT, finrank_top,
    finrank_eq_eight, boundary_finrank] at h
  omega

theorem totalX_kernel_finrank : finrank F (LinearMap.ker totalX) = 76 :=
  kernel_finrank totalX totalX_surjective

theorem totalZ_kernel_finrank : finrank F (LinearMap.ker totalZ) = 76 :=
  kernel_finrank totalZ totalZ_surjective

/-- A chosen charge has matching low/high residues with zero total residue. -/
theorem split_liftX (a : A) : ∃ b : Boundary, totalX b = 0 ∧ leftX b = a := by
  exact BoundaryCharge.split_lift lowX highX lowX_surjective highX_surjective a

theorem split_liftZ (a : A) : ∃ b : Boundary, totalZ b = 0 ∧ leftZ b = a := by
  exact BoundaryCharge.split_lift lowZ highZ lowZ_surjective highZ_surjective a

/-- Low-side charge on boundary coordinates whose total residue vanishes. -/
def chargeX : LinearMap.ker totalX →ₗ[F] A := leftX.domRestrict (LinearMap.ker totalX)

def chargeZ : LinearMap.ker totalZ →ₗ[F] A := leftZ.domRestrict (LinearMap.ker totalZ)

theorem chargeX_surjective : Function.Surjective chargeX := by
  intro a
  obtain ⟨b, hb, ha⟩ := split_liftX a
  exact ⟨⟨b, hb⟩, ha⟩

theorem chargeZ_surjective : Function.Surjective chargeZ := by
  intro a
  obtain ⟨b, hb, ha⟩ := split_liftZ a
  exact ⟨⟨b, hb⟩, ha⟩

end
end QldpcVerification.Planar.BoundaryResidue
