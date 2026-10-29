import QldpcVerification.Lattice.Displacement
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Connected incidence matrices have rank at least the vertex count minus one. -/

namespace QldpcVerification.Lattice

open Matrix Module

variable {E V : Type} [Fintype V] [DecidableEq V]

theorem transpose_incidence_apply (source target : E → V)
    (H : Matrix V E (ZMod 2)) (hH : ∀ v e, H v e = incidence source target e v)
    (f : V → ZMod 2) (e : E) :
    H.transpose.mulVec f e = f (source e) + f (target e) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hH, incidence, add_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
  simp

theorem incidence_rank_lower (source target : E → V) (base : V)
    (H : Matrix V E (ZMod 2)) (hH : ∀ v e, H v e = incidence source target e v)
    (hconn : ∀ f : V → ZMod 2, (∀ e, f (source e) = f (target e)) → ∀ v, f v = f base) :
    Fintype.card V - 1 ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) := by
  classical
  let K := LinearMap.ker H.transpose.mulVecLin
  have hc (f : K) : ∀ v, (f : V → ZMod 2) v = (f : V → ZMod 2) base := by
    apply hconn
    intro e
    have he := congrFun (show H.transpose.mulVec (f : V → ZMod 2) = 0 from f.property) e
    rw [transpose_incidence_apply source target H hH] at he
    have hh : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact hh _ _ he
  let ev : K →ₗ[ZMod 2] ZMod 2 := {
    toFun := fun f => (f : V → ZMod 2) base
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hi : Function.Injective ev := by
    intro f g hfg
    apply Subtype.ext
    funext v
    exact (hc f v).trans (hfg.trans (hc g v).symm)
  have hk : finrank (ZMod 2) K ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective hi
  have hr := LinearMap.finrank_range_add_finrank_ker H.transpose.mulVecLin
  rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at hr
  change finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) + finrank (ZMod 2) K =
    Fintype.card V at hr
  omega

theorem constant_of_periodic {m : ℕ} [NeZero m] {A : Type}
    (f : ZMod m → A) (a b : ZMod m) (hi : b * a = 1)
    (hp : ∀ v, f (v + a) = f v) (v : ZMod m) : f v = f 0 := by
  have hn : ∀ n : ℕ, f ((n : ZMod m) * a) = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have he : ((n + 1 : ℕ) : ZMod m) * a = (n : ZMod m) * a + a := by push_cast; ring
      rw [he, hp, ih]
  have he : (((v * b).val : ℕ) : ZMod m) * a = v := by
    rw [ZMod.natCast_zmod_val, mul_assoc, hi, mul_one]
  simpa only [he] using hn (v * b).val

end QldpcVerification.Lattice
