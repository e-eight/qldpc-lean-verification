import QldpcVerification.Lattice.IncidenceRank
import Mathlib.Data.Int.GCD

/-! Joint cyclic generators give connectivity without an invertible individual step. -/

namespace QldpcVerification.Lattice

open Matrix Module

theorem incidence_rank_eq {E V : Type} [Fintype V] [DecidableEq V]
    (source target : E → V) (base : V)
    (H : Matrix V E (ZMod 2)) (hH : ∀ v e, H v e = incidence source target e v)
    (hconn : ∀ f : V → ZMod 2, (∀ e, f (source e) = f (target e)) → ∀ v, f v = f base) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) = Fintype.card V - 1 := by
  have hl := incidence_rank_lower source target base H hH hconn
  let K := LinearMap.ker H.transpose.mulVecLin
  have hone : (fun _ : V => (1 : ZMod 2)) ∈ K := by
    change H.transpose.mulVec (fun _ => 1) = 0
    funext e
    rw [transpose_incidence_apply source target H hH]
    change (1 : ZMod 2) + 1 = 0
    decide
  have hk : 1 ≤ finrank (ZMod 2) K := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    have hz : (fun _ : V => (1 : ZMod 2)) = 0 := by
      simpa only [he, Submodule.mem_bot] using hone
    have hh := congrFun hz base
    norm_num at hh
  have hr := LinearMap.finrank_range_add_finrank_ker H.transpose.mulVecLin
  rw [Matrix.range_mulVecLin, Module.finrank_fintype_fun_eq_card] at hr
  change finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) +
    finrank (ZMod 2) K = Fintype.card V at hr
  omega

theorem exists_unit_combination {m : ℕ} (s t : ℕ)
    (hc : Nat.gcd (Nat.gcd s t) m = 1) :
    ∃ u v : ZMod m, u * (s : ZMod m) + v * (t : ZMod m) = 1 := by
  have hst : (Nat.gcd s t : ZMod m) =
      (s : ZMod m) * ((Nat.gcdA s t : ℤ) : ZMod m) +
      (t : ZMod m) * ((Nat.gcdB s t : ℤ) : ZMod m) := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) (Nat.gcd_eq_gcd_ab s t)
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_mul] using h
  have hgm : (1 : ZMod m) = (Nat.gcd s t : ZMod m) *
      ((Nat.gcdA (Nat.gcd s t) m : ℤ) : ZMod m) := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) (Nat.gcd_eq_gcd_ab (Nat.gcd s t) m)
    simpa [hc] using h
  refine ⟨((Nat.gcdA s t : ℤ) : ZMod m) * ((Nat.gcdA (Nat.gcd s t) m : ℤ) : ZMod m),
    ((Nat.gcdB s t : ℤ) : ZMod m) * ((Nat.gcdA (Nat.gcd s t) m : ℤ) : ZMod m), ?_⟩
  rw [hst] at hgm
  linear_combination -hgm

theorem periodic_nat_multiple {m : ℕ} {A : Type} (f : ZMod m → A) (a : ZMod m)
    (hp : ∀ v, f (v + a) = f v) (n : ℕ) (v : ZMod m) :
    f (v + (n : ZMod m) * a) = f v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : v + ((n + 1 : ℕ) : ZMod m) * a = (v + (n : ZMod m) * a) + a := by
      push_cast
      ring
    rw [he, hp, ih]

theorem constant_of_joint_periodic {m : ℕ} [NeZero m] {A : Type}
    (f : ZMod m → A) (s t : ℕ) (hc : Nat.gcd (Nat.gcd s t) m = 1)
    (hs : ∀ v, f (v + (s : ZMod m)) = f v)
    (ht : ∀ v, f (v + (t : ZMod m)) = f v) (v : ZMod m) : f v = f 0 := by
  obtain ⟨u, w, hw⟩ := exists_unit_combination s t hc
  have hp (x : ZMod m) : f (x + 1) = f x := by
    calc
      f (x + 1) = f ((x + u * (s : ZMod m)) + w * (t : ZMod m)) := by
        congr 1
        rw [← hw]
        ring
      _ = f (x + u * (s : ZMod m)) := by
        simpa only [ZMod.natCast_zmod_val] using
          periodic_nat_multiple f (t : ZMod m) ht w.val (x + u * (s : ZMod m))
      _ = f x := by
        simpa only [ZMod.natCast_zmod_val] using
          periodic_nat_multiple f (s : ZMod m) hs u.val x
  exact constant_of_periodic f 1 1 (by simp) hp v

end QldpcVerification.Lattice
