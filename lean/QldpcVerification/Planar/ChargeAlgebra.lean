import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The actual722 bulk charge algebra, in both coordinate presentations.

The construction uses monic quotients, not fields: no irreducibility hypothesis
is needed. All identities are symbolic characteristic-two ring calculations.
See `analytical/notes/algebra.md`, §8.1. The coordinate surjectivity statements
are algebraic inputs to the boundary-charge argument, not a distance theorem.
-/

namespace QldpcVerification.Planar.ChargeAlgebra

open Polynomial Module
open scoped CharTwo

noncomputable section

abbrev F := ZMod 2

def r : F[X] := 1 + X + X ^ 2 + X ^ 6 + X ^ 8

def p : F[X] := X ^ 8 + X ^ 5 + 1

theorem r_monic : r.Monic := by
  unfold r
  monicity!

theorem r_natDegree : r.natDegree = 8 := by
  unfold r
  compute_degree!

theorem p_monic : p.Monic := by
  unfold p
  monicity!

theorem p_natDegree : p.natDegree = 8 := by
  unfold p
  compute_degree!

abbrev A := AdjoinRoot r

instance : Nontrivial A := AdjoinRoot.nontrivial (f := r) (by
  rw [Polynomial.degree_eq_natDegree r_monic.ne_zero, r_natDegree]
  norm_num)

instance : CharP A 2 := charP_of_injective_algebraMap' F 2

instance : Module.Finite F A := r_monic.finite_adjoinRoot

instance : Module.Finite F (AdjoinRoot p) := p_monic.finite_adjoinRoot

def y : A := AdjoinRoot.root r

def t : A := y + y ^ 2

def x : A := 1 + y ^ 2 + y ^ 5 + y ^ 6

def yPowerBasis : PowerBasis F A := AdjoinRoot.powerBasis' r_monic

theorem finrank_eq_eight : Module.finrank F A = 8 := by
  rw [yPowerBasis.finrank]
  exact r_natDegree

theorem r_y : 1 + y + y ^ 2 + y ^ 6 + y ^ 8 = 0 := by
  simpa [r, y] using AdjoinRoot.eval₂_root r

theorem t_mul_inverse : t * (1 + y ^ 5 + y ^ 6) = 1 := by
  calc
    t * (1 + y ^ 5 + y ^ 6) = (1 + y + y ^ 2 + y ^ 6 + y ^ 8) + 1 := by
      unfold t
      ring_nf <;> simp
    _ = 1 := by rw [r_y]; simp

theorem y_mul_inverse : y * (1 + y + y ^ 5 + y ^ 7) = 1 := by
  calc
    y * (1 + y + y ^ 5 + y ^ 7) = (1 + y + y ^ 2 + y ^ 6 + y ^ 8) + 1 := by
      ring_nf <;> simp
    _ = 1 := by rw [r_y]; simp

theorem x_sq : x ^ 2 = 1 + y ^ 5 + y ^ 6 := by
  calc
    x ^ 2 = y ^ 4 * (1 + y + y ^ 2 + y ^ 6 + y ^ 8) +
        (1 + y ^ 5 + y ^ 6) := by
      unfold x
      ring_nf <;> simp
    _ = 1 + y ^ 5 + y ^ 6 := by rw [r_y]; simp

theorem x_sq_mul_t : x ^ 2 * t = 1 := by
  rw [x_sq, mul_comm]
  exact t_mul_inverse

theorem x_relation : x + x ^ 2 + y ^ 2 = 0 := by
  rw [x_sq]
  unfold x
  ring_nf <;> simp

/-- The actual722 second bulk generator vanishes. -/
theorem g_relation : 1 + x ^ 2 * y + x ^ 2 * y ^ 2 = 0 := by
  calc
    1 + x ^ 2 * y + x ^ 2 * y ^ 2 = 1 + x ^ 2 * t := by unfold t; ring
    _ = 0 := by rw [x_sq_mul_t]; simp

def yUnit : Aˣ where
  val := y
  inv := 1 + y + y ^ 5 + y ^ 7
  val_inv := y_mul_inverse
  inv_val := by rw [mul_comm]; exact y_mul_inverse

def xUnit : Aˣ where
  val := x
  inv := x * t
  val_inv := by simpa [pow_two, mul_assoc] using x_sq_mul_t
  inv_val := by simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using x_sq_mul_t

theorem y_isUnit : IsUnit y := ⟨yUnit, rfl⟩

theorem x_isUnit : IsUnit x := ⟨xUnit, rfl⟩

theorem p_x : x ^ 8 + x ^ 5 + 1 = 0 := by
  have h : x + x ^ 4 + t ^ 2 = 0 := by
    calc
      x + x ^ 4 + t ^ 2 =
          (x + x ^ 2 + y ^ 2) ^ 2 + (x + x ^ 2 + y ^ 2) := by
        unfold t
        ring_nf <;> simp
      _ = 0 := by rw [x_relation]; simp
  calc
    x ^ 8 + x ^ 5 + 1 =
        x ^ 4 * (x + x ^ 4 + t ^ 2) + (x ^ 2 * t) ^ 2 + 1 := by
      ring_nf <;> simp
    _ = 0 := by rw [h, x_sq_mul_t]; simp

theorem t_eq_x_polynomial : t = x ^ 6 + x ^ 3 := by
  calc
    t = t * (x ^ 8 + x ^ 5 + 1) + (x ^ 6 + x ^ 3) * (x ^ 2 * t) := by
      ring_nf <;> simp
    _ = x ^ 6 + x ^ 3 := by rw [p_x, x_sq_mul_t]; simp

/-- Polynomial form of `y = x⁻² + x + x²`, avoiding division in a ring. -/
theorem y_eq_x_polynomial : y = x ^ 6 + x ^ 3 + x + x ^ 2 := by
  calc
    y = (x + x ^ 2 + y ^ 2) + (t + x + x ^ 2) := by
      unfold t
      ring_nf <;> simp
    _ = x ^ 6 + x ^ 3 + x + x ^ 2 := by
      rw [x_relation, t_eq_x_polynomial]; simp

/-- Substitution of the horizontal coordinate into the second monic quotient. -/
def xPresentation : AdjoinRoot p →ₐ[F] A :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId F A) x (by simpa [p] using p_x)

@[simp] theorem xPresentation_root : xPresentation (AdjoinRoot.root p) = x := by
  simp [xPresentation]

theorem xPresentation_surjective : Function.Surjective xPresentation := by
  apply (AlgHom.range_eq_top xPresentation).mp
  apply top_unique
  rw [← AdjoinRoot.adjoinRoot_eq_top (f := r)]
  apply Algebra.adjoin_le
  intro z hz
  have hz' : z = y := Set.mem_singleton_iff.mp hz
  rw [hz', y_eq_x_polynomial]
  have hx : x ∈ xPresentation.range := ⟨AdjoinRoot.root p, xPresentation_root⟩
  exact xPresentation.range.add_mem
    (xPresentation.range.add_mem
      (xPresentation.range.add_mem (xPresentation.range.pow_mem hx 6)
        (xPresentation.range.pow_mem hx 3)) hx) (xPresentation.range.pow_mem hx 2)

/-- Equivalence of the two degree-eight presentations; neither polynomial is assumed irreducible. -/
def xEquiv : AdjoinRoot p ≃ₐ[F] A :=
  AlgEquiv.ofBijective xPresentation ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := xPresentation.toLinearMap) (by
        rw [(AdjoinRoot.powerBasis' p_monic).finrank, finrank_eq_eight]
        exact p_natDegree)).mpr xPresentation_surjective,
    xPresentation_surjective⟩

def xPowerBasis : PowerBasis F A := (AdjoinRoot.powerBasis' p_monic).map xEquiv

@[simp] theorem xPowerBasis_gen : xPowerBasis.gen = x := xPresentation_root

/-- Vertical coordinate basis `1,y,…,y⁷`. -/
def yBasis : Basis (Fin 8) F A := yPowerBasis.basis.reindex (finCongr r_natDegree)

/-- Horizontal coordinate basis `1,x,…,x⁷`. -/
def xBasis : Basis (Fin 8) F A := xPowerBasis.basis.reindex (finCongr p_natDegree)

@[simp] theorem yBasis_apply (i : Fin 8) : yBasis i = y ^ (i : ℕ) := by
  rw [yBasis, Basis.reindex_apply, yPowerBasis.basis_eq_pow]
  rfl

@[simp] theorem xBasis_apply (i : Fin 8) : xBasis i = x ^ (i : ℕ) := by
  rw [xBasis, Basis.reindex_apply, xPowerBasis.basis_eq_pow, xPowerBasis_gen]
  rfl

theorem span_y_powers : Submodule.span F (Set.range (fun i : Fin 8 => y ^ (i : ℕ))) = ⊤ := by
  have hb : (fun i : Fin 8 => y ^ (i : ℕ)) = yBasis := by
    funext i
    exact (yBasis_apply i).symm
  rw [hb]
  exact yBasis.span_eq

theorem span_x_powers : Submodule.span F (Set.range (fun i : Fin 8 => x ^ (i : ℕ))) = ⊤ := by
  have hb : (fun i : Fin 8 => x ^ (i : ℕ)) = xBasis := by
    funext i
    exact (xBasis_apply i).symm
  rw [hb]
  exact xBasis.span_eq

/-- Coefficients on eight consecutive vertical sites realize every bulk charge. -/
theorem y_coordinates_surjective :
    Function.Surjective (fun c : Fin 8 → F => ∑ i, c i • y ^ (i : ℕ)) := by
  intro a
  exact ⟨yBasis.equivFun a, by simpa only [yBasis_apply] using yBasis.sum_equivFun a⟩

/-- Coefficients on eight consecutive horizontal sites realize every bulk charge. -/
theorem x_coordinates_surjective :
    Function.Surjective (fun c : Fin 8 → F => ∑ i, c i • x ^ (i : ℕ)) := by
  intro a
  exact ⟨xBasis.equivFun a, by simpa only [xBasis_apply] using xBasis.sum_equivFun a⟩

end
end QldpcVerification.Planar.ChargeAlgebra
