import QldpcVerification.Bicycle.Connected

/-! A primitive integer step pair and a unimodular complement for joint cyclic generators. -/

namespace QldpcVerification.Bicycle.Connected

open Lattice

structure PeriodBasis (m s t : ℕ) where
  a : ℤ
  b : ℤ
  p : ℤ
  q : ℤ
  scale : (ZMod m)ˣ
  first_step : (s : ZMod m) = (scale : ZMod m) * (a : ZMod m)
  second_step : (t : ZMod m) = (scale : ZMod m) * (b : ZMod m)
  bezout : a * p + b * q = 1

theorem periodBasis_nonempty {m s t : ℕ}
    (hc : Nat.gcd (Nat.gcd s t) m = 1) : Nonempty (PeriodBasis m s t) := by
  by_cases hg : Nat.gcd s t = 0
  · have hm : m = 1 := by simpa [hg] using hc
    subst m
    exact ⟨⟨1, 0, 1, 0, 1, Subsingleton.elim _ _, Subsingleton.elim _ _, by norm_num⟩⟩
  · have hpos : 0 < Int.gcd (s : ℤ) (t : ℤ) := by
      simpa using Nat.pos_of_ne_zero hg
    obtain ⟨a, b, hab, hs, ht⟩ := Int.exists_gcd_one hpos
    refine ⟨{
      a := a, b := b, p := Int.gcdA a b, q := Int.gcdB a b
      scale := ZMod.unitOfCoprime (Nat.gcd s t) hc
      first_step := ?_
      second_step := ?_
      bezout := ?_ }⟩
    · have h := congrArg (fun z : ℤ => (z : ZMod m)) hs
      simpa [mul_comm] using h
    · have h := congrArg (fun z : ℤ => (z : ZMod m)) ht
      simpa [mul_comm] using h
    · have h := Int.gcd_eq_gcd_ab a b
      simpa [hab] using h.symm

noncomputable def periodBasis {m s t : ℕ}
    (hc : Nat.gcd (Nat.gcd s t) m = 1) : PeriodBasis m s t :=
  Classical.choice (periodBasis_nonempty hc)

namespace PeriodBasis

variable {m s t : ℕ} [NeZero m] (B : PeriodBasis m s t)

def potential (v : ZMod m) : ℤ := (((B.scale⁻¹ : (ZMod m)ˣ) : ZMod m) * v).val

def lift : WindingData (source (m := m)) (target s t) Normalized.horizontal where
  a := B.a
  b := B.b
  period := m
  period_ne_zero := by exact_mod_cast (NeZero.ne m)
  potential := B.potential
  carry e := (B.a * axisX Normalized.horizontal e + B.b * axisY Normalized.horizontal e -
    (B.potential (target s t e) - B.potential (source e))) / m
  edge_eq e := by
    have hp (v : ZMod m) : (B.potential v : ZMod m) =
        ((B.scale⁻¹ : (ZMod m)ˣ) : ZMod m) * v := by
      simp [potential]
    have hs : ((B.scale⁻¹ : (ZMod m)ˣ) : ZMod m) * (s : ZMod m) = (B.a : ZMod m) := by
      rw [B.first_step, ← mul_assoc, Units.inv_mul, one_mul]
    have ht : ((B.scale⁻¹ : (ZMod m)ˣ) : ZMod m) * (t : ZMod m) = (B.b : ZMod m) := by
      rw [B.second_step, ← mul_assoc, Units.inv_mul, one_mul]
    have he : (B.a : ZMod m) * (axisX Normalized.horizontal e : ZMod m) +
        (B.b : ZMod m) * (axisY Normalized.horizontal e : ZMod m) =
        (B.potential (target s t e) : ZMod m) - (B.potential (source e) : ZMod m) := by
      rw [hp, hp]
      cases e <;> simp [target, source, Normalized.source, Normalized.horizontal,
        axisX, axisY, mul_add, hs, ht]
    have hd : (m : ℤ) ∣ B.a * axisX Normalized.horizontal e +
        B.b * axisY Normalized.horizontal e -
        (B.potential (target s t e) - B.potential (source e)) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul] using sub_eq_zero.mpr he
    rw [mul_comm (m : ℤ), Int.ediv_mul_cancel hd]
    ring

def label (e : Edge m) : ZMod 2 × ZMod 2 :=
  (((B.lift).carry e : ZMod 2),
    ((B.q * axisX Normalized.horizontal e - B.p * axisY Normalized.horizontal e : ℤ) : ZMod 2))

theorem label_sum {u v : ZMod m} (w : Walk source (target s t) u v) :
    (w.edges.map B.label).sum =
      (((B.lift).walkCarry w : ZMod 2),
        ((B.q * (w.displacement Normalized.horizontal).1 -
          B.p * (w.displacement Normalized.horizontal).2 : ℤ) : ZMod 2)) := by
  induction w with
  | nil => simp [Walk.edges, Walk.displacement, WindingData.walkCarry]; rfl
  | cons e r w ih =>
    have hn : ∀ z : ZMod 2, -z = z := by decide
    cases r <;> simp [Walk.edges, List.map_cons, List.sum_cons, ih, label,
      WindingData.walkCarry, Walk.displacement, signed, mul_add, hn] <;> ring

theorem closed_zero {v : ZMod m} (w : Walk source (target s t) v v)
    (hz : w.displacement Normalized.horizontal = 0) : (w.edges.map B.label).sum = 0 := by
  have h := B.lift.displacement_eq w
  rw [hz] at h
  have hc : B.lift.walkCarry w = 0 := by
    have hm : (m : ℤ) * B.lift.walkCarry w = 0 := by simpa [lift] using h.symm
    exact (mul_eq_zero.mp hm).resolve_left (by exact_mod_cast (NeZero.ne m))
  rw [B.label_sum, hz, hc]
  simp

end PeriodBasis
end QldpcVerification.Bicycle.Connected
