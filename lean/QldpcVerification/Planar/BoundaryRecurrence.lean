import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Directional boundary recurrences

Analytic independence for the two truncations in `analytical/notes/geometry.md`,
Lemma 1. Array index `k` represents anchor coordinate `k - 2`. There are `n`
retained slices and `n + 2` anchor slices. The transverse coordinate is encoded
as an ordinary polynomial, without quotienting by a periodicity relation.

The generic statements work over any commutative domain, with signed
eliminants; in characteristic two these are precisely the note's eliminants.
The final maps accept finite scalar arrays, not a single scalar unknown.

Finite coefficient projection is proved faithful using a support bound, giving
rank 357 for each explicit 722-coordinate directional map. Not yet transported
here: the submitted JSON rows, their ordering, and the Z reflection/component
exchange. No commutation, encoded-dimension, or distance claim is made by this
module. No computational rank certificate is used.
-/

namespace QldpcVerification.Planar.BoundaryRecurrence

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Two adjacent X equations force the first two anchor slices to vanish. -/
theorem x_initial (s t u v w z : R)
    (hd : (1 - s * t) ^ 2 + t ≠ 0)
    (h₀ : u + v + s * w = 0) (h₁ : t * u + w = 0)
    (h₂ : v + w + s * z = 0) (h₃ : t * v + z = 0) :
    u = 0 ∧ v = 0 := by
  have hv : (1 - s * t) * u + v = 0 := by
    linear_combination h₀ - s * h₁
  have hw : (1 - s * t) * v + w = 0 := by
    linear_combination h₂ - s * h₃
  have hu : ((1 - s * t) ^ 2 + t) * u = 0 := by
    linear_combination (1 - s * t) * hv - hw + h₁
  have hu0 : u = 0 := (mul_eq_zero.mp hu).resolve_left hd
  exact ⟨hu0, by simpa [hu0] using hv⟩

/-- Two adjacent Z equations force the first two anchor slices to vanish. -/
theorem z_initial (a q u v w z : R)
    (hq : q ≠ 0) (hd : (1 - q * a) ^ 2 + q ^ 2 * a ≠ 0)
    (h₀ : u + a * w = 0) (h₁ : w + q * v + q * u = 0)
    (h₂ : v + a * z = 0) (h₃ : z + q * w + q * v = 0) :
    u = 0 ∧ v = 0 := by
  have hw : (1 - q * a) * w + q * v = 0 := by
    linear_combination h₁ - q * h₀
  have hz : (1 - q * a) * z + q * w = 0 := by
    linear_combination h₃ - q * h₂
  have he : ((1 - q * a) ^ 2 + q ^ 2 * a) * z = 0 := by
    linear_combination (1 - q * a) * hz - q * hw + q ^ 2 * h₂
  have hz0 : z = 0 := (mul_eq_zero.mp he).resolve_left hd
  have hw0 : w = 0 := (mul_eq_zero.mp (by simpa [hz0] using hz)).resolve_left hq
  exact ⟨by simpa [hw0] using h₀, by simpa [hz0] using h₂⟩

/-- Vanishing on `n ≥ 2` retained X slices kills all `n + 2` anchor slices. -/
theorem x_recurrence_zero {n : ℕ} (hn : 2 ≤ n) (s t : R)
    (hd : (1 - s * t) ^ 2 + t ≠ 0) (c : ℕ → R)
    (hf : ∀ i < n, c i + c (i + 1) + s * c (i + 2) = 0)
    (hg : ∀ i < n, t * c i + c (i + 2) = 0) :
    ∀ k < n + 2, c k = 0 := by
  obtain ⟨h₀, h₁⟩ := x_initial s t (c 0) (c 1) (c 2) (c 3) hd
    (hf 0 (by omega)) (hg 0 (by omega))
    (hf 1 (by omega)) (hg 1 (by omega))
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases k with _ | k
    · exact h₀
    rcases k with _ | k
    · exact h₁
    have hc := ih k (by omega) (by omega)
    simpa [hc, Nat.succ_eq_add_one, Nat.add_assoc] using hg k (by omega)

/-- The Z first equation propagates vanishing because `a` is not zero. -/
theorem z_recurrence_zero {n : ℕ} (hn : 2 ≤ n) (a q : R)
    (ha : a ≠ 0) (hq : q ≠ 0) (hd : (1 - q * a) ^ 2 + q ^ 2 * a ≠ 0)
    (c : ℕ → R)
    (hf : ∀ i < n, c i + a * c (i + 2) = 0)
    (hg : ∀ i < n, c (i + 2) + q * c (i + 1) + q * c i = 0) :
    ∀ k < n + 2, c k = 0 := by
  obtain ⟨h₀, h₁⟩ := z_initial a q (c 0) (c 1) (c 2) (c 3) hq hd
    (hf 0 (by omega)) (hg 0 (by omega))
    (hf 1 (by omega)) (hg 1 (by omega))
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rcases k with _ | k
    · exact h₀
    rcases k with _ | k
    · exact h₁
    have hc := ih k (by omega) (by omega)
    have hm : a * c (k + 2) = 0 := by simpa [hc] using hf k (by omega)
    exact (mul_eq_zero.mp hm).resolve_left ha

/-- Extend a finite array by zero, solely to simplify recurrence indexing. -/
def entry {N : ℕ} (c : Fin N → R) (k : ℕ) : R :=
  if h : k < N then c ⟨k, h⟩ else 0

@[simp] theorem entry_fin {N : ℕ} (c : Fin N → R) (k : Fin N) : entry c k = c k := by
  simp [entry, k.isLt]

@[simp] theorem entry_add {N : ℕ} (c d : Fin N → R) (k : ℕ) :
    entry (c + d) k = entry c k + entry d k := by
  unfold entry
  split <;> simp_all

@[simp] theorem entry_smul {N : ℕ} (r : R) (c : Fin N → R) (k : ℕ) :
    entry (r • c) k = r * entry c k := by
  unfold entry
  split <;> simp_all [smul_eq_mul]

/-- Directional X truncation: both physical components at each retained slice. -/
def xMap (n : ℕ) (s t : R) : (Fin (n + 2) → R) →ₗ[R] (Fin n → R × R) where
  toFun c i := (entry c i + entry c (i.val + 1) + s * entry c (i.val + 2),
    t * entry c i + entry c (i.val + 2))
  map_add' c d := by
    ext i <;> simp [mul_add] <;> ring
  map_smul' r c := by
    ext i <;> simp [smul_eq_mul] <;> ring

/-- Directional Z truncation after reflection and exchange of components. -/
def zMap (n : ℕ) (a q : R) : (Fin (n + 2) → R) →ₗ[R] (Fin n → R × R) where
  toFun c i := (entry c i + a * entry c (i.val + 2),
    entry c (i.val + 2) + q * entry c (i.val + 1) + q * entry c i)
  map_add' c d := by
    ext i <;> simp [mul_add] <;> ring
  map_smul' r c := by
    ext i <;> simp [smul_eq_mul] <;> ring

theorem xMap_injective {n : ℕ} (hn : 2 ≤ n) (s t : R)
    (hd : (1 - s * t) ^ 2 + t ≠ 0) : Function.Injective (xMap n s t) := by
  suffices hz : ∀ c, xMap n s t c = 0 → c = 0 by
    intro c d h
    have he : xMap n s t (c - d) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hz (c - d) he)
  intro c h
  have hf (i : ℕ) (hi : i < n) := congrArg (fun v => (v ⟨i, hi⟩).1) h
  have hg (i : ℕ) (hi : i < n) := congrArg (fun v => (v ⟨i, hi⟩).2) h
  have hz := x_recurrence_zero hn s t hd (entry c) hf hg
  funext k
  simpa using hz k k.isLt

theorem zMap_injective {n : ℕ} (hn : 2 ≤ n) (a q : R)
    (ha : a ≠ 0) (hq : q ≠ 0) (hd : (1 - q * a) ^ 2 + q ^ 2 * a ≠ 0) :
    Function.Injective (zMap n a q) := by
  suffices hz : ∀ c, zMap n a q c = 0 → c = 0 by
    intro c d h
    have he : zMap n a q (c - d) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hz (c - d) he)
  intro c h
  have hf (i : ℕ) (hi : i < n) := congrArg (fun v => (v ⟨i, hi⟩).1) h
  have hg (i : ℕ) (hi : i < n) := congrArg (fun v => (v ⟨i, hi⟩).2) h
  have hz := z_recurrence_zero hn a q ha hq hd (entry c) hf hg
  funext k
  simpa using hz k k.isLt

end Domain

abbrev F2 := ZMod 2
abbrev P := Polynomial F2

open Polynomial

/-- A constant coefficient of one proves nonvanishing without expanding powers. -/
theorem x_eliminant_ne_zero :
    (1 - (X : P) ^ 2 * (X + X ^ 2)) ^ 2 + (X + X ^ 2) ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (0 : F2)) h
  simpa using he

theorem z_eliminant_ne_zero :
    (1 - (X : P) ^ 2 * (X + X ^ 2)) ^ 2 + (X ^ 2) ^ 2 * (X + X ^ 2) ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (0 : F2)) h
  simpa using he

theorem transverse_factor_ne_zero : (X : P) + X ^ 2 ≠ 0 := by
  intro h
  have he := congrArg (fun p : P => p.coeff 1) h
  simpa using he

theorem xPolynomial_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (xMap n ((X : P) ^ 2) (X + X ^ 2)) :=
  xMap_injective hn _ _ x_eliminant_ne_zero

theorem zPolynomial_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (zMap n ((X : P) + X ^ 2) (X ^ 2)) :=
  zMap_injective hn _ _ transverse_factor_ne_zero
    (pow_ne_zero 2 Polynomial.X_ne_zero) z_eliminant_ne_zero

/-- Pack the transverse coordinate of a finite scalar array as polynomial coefficients. -/
noncomputable def pack (N m : ℕ) :
    (Fin N → Fin m → F2) →ₗ[F2] (Fin N → P) where
  toFun c i := ∑ j : Fin m, monomial j.val (c i j)
  map_add' c d := by
    funext i
    simp [map_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext i
    simp [Finset.smul_sum, Polynomial.smul_monomial]

@[simp] theorem pack_coeff {N m : ℕ} (c : Fin N → Fin m → F2)
    (i : Fin N) (j : Fin m) : (pack N m c i).coeff j.val = c i j := by
  classical
  change (∑ k : Fin m, monomial k.val (c i k)).coeff j.val = c i j
  simp only [finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [show k.val ≠ j.val from fun h => hkj (Fin.ext h)]
  · simp

theorem pack_injective (N m : ℕ) : Function.Injective (pack N m) := by
  intro c d h
  funext i j
  have he := congrArg (fun v : Fin N → P => (v i).coeff j.val) h
  simpa using he

/-- X check synthesis for finite scalar anchor arrays; output slices are polynomials. -/
noncomputable def xChecks (n m : ℕ) :
    (Fin (n + 2) → Fin m → F2) →ₗ[F2] (Fin n → P × P) :=
  ((xMap n ((X : P) ^ 2) (X + X ^ 2)).restrictScalars F2).comp (pack (n + 2) m)

/-- Reflected Z check synthesis for finite scalar anchor arrays. -/
noncomputable def zChecks (n m : ℕ) :
    (Fin (n + 2) → Fin m → F2) →ₗ[F2] (Fin n → P × P) :=
  ((zMap n ((X : P) + X ^ 2) (X ^ 2)).restrictScalars F2).comp (pack (n + 2) m)

theorem xChecks_injective {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Function.Injective (xChecks n m) :=
  (xPolynomial_injective hn).comp (pack_injective (n + 2) m)

theorem zChecks_injective {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Function.Injective (zChecks n m) :=
  (zPolynomial_injective hn).comp (pack_injective (n + 2) m)

/-- The 21 by 17 X anchor coefficient array is recovered uniquely. -/
theorem xChecks722_injective : Function.Injective (xChecks 19 17) :=
  xChecks_injective (by omega) 17

/-- The reflected 21 by 17 Z anchor coefficient array is recovered uniquely. -/
theorem zChecks722_injective : Function.Injective (zChecks 19 17) :=
  zChecks_injective (by omega) 17

end QldpcVerification.Planar.BoundaryRecurrence

namespace QldpcVerification.Planar.BoundaryRecurrence

/-- Unreflected physical coordinates, compatible with `Planar.Commutation.Q`. -/
abbrev PhysicalQ := Bool × (Fin 19 × Fin 19)
abbrev XAnchor := Fin 21 × Fin 17
abbrev ZAnchor := Fin 17 × Fin 21

/-- The X recurrence's first array index is the anchor row plus two. -/
def xAnchorCoordinates : (XAnchor → F2) ≃ₗ[F2] (Fin 21 → Fin 17 → F2) where
  toFun c i j := c (i, j)
  invFun c a := c a.1 a.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Z reflection: `(c + 2, d)` becomes transverse `16 - c`, directional `20 - d`. -/
def zAnchorCoordinates : (ZAnchor → F2) ≃ₗ[F2] (Fin 21 → Fin 17 → F2) where
  toFun c i j := c (j.rev, i.rev)
  invFun c a := c a.2.rev a.1.rev
  left_inv c := by
    funext a
    simp
  right_inv c := by
    funext i j
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `false` is block A, `true` is block B; row precedes column. -/
def xPhysicalCoordinates :
    (Fin 19 → Fin 19 → F2 × F2) ≃ₗ[F2] (PhysicalQ → F2) where
  toFun v q := if q.1 then (v q.2.1 q.2.2).2 else (v q.2.1 q.2.2).1
  invFun v i j := (v (false, (i, j)), v (true, (i, j)))
  left_inv _ := rfl
  right_inv v := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> rfl
  map_add' v w := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> rfl
  map_smul' r v := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> rfl

/-- Undo the Z reflection, exchange blocks, and restore row/column order. -/
def zPhysicalCoordinates :
    (Fin 19 → Fin 19 → F2 × F2) ≃ₗ[F2] (PhysicalQ → F2) where
  toFun v q := if q.1 then (v q.2.2.rev q.2.1.rev).1
    else (v q.2.2.rev q.2.1.rev).2
  invFun v i j := (v (true, (j.rev, i.rev)), v (false, (j.rev, i.rev)))
  left_inv v := by
    funext i j
    simp
  right_inv v := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> simp
  map_add' v w := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> rfl
  map_smul' r v := by
    funext q
    rcases q with ⟨b, i, j⟩
    cases b <;> rfl

end QldpcVerification.Planar.BoundaryRecurrence

namespace QldpcVerification.Planar.BoundaryRecurrence

open Polynomial

/-- All coefficients from `b` onward vanish (equivalently degree strictly below `b`). -/
def supportedBelow (b : ℕ) (p : P) : Prop := ∀ k, b ≤ k → p.coeff k = 0

theorem supportedBelow_mono {b B : ℕ} {p : P} (h : supportedBelow b p)
    (hb : b ≤ B) : supportedBelow B p :=
  fun k hk => h k (hb.trans hk)

theorem supportedBelow_add {b : ℕ} {p q : P}
    (hp : supportedBelow b p) (hq : supportedBelow b q) : supportedBelow b (p + q) := by
  intro k hk
  simp [coeff_add, hp k hk, hq k hk]

theorem supportedBelow_Xpow {b : ℕ} {p : P} (hp : supportedBelow b p) (d : ℕ) :
    supportedBelow (b + d) ((X : P) ^ d * p) := by
  intro k hk
  rw [coeff_X_pow_mul', if_pos (by omega)]
  exact hp (k - d) (by omega)

theorem supportedBelow_transverse {b : ℕ} {p : P} (hp : supportedBelow b p) :
    supportedBelow (b + 2) (((X : P) + X ^ 2) * p) := by
  rw [add_mul]
  apply supportedBelow_add
  · have h := supportedBelow_Xpow hp 1
    simp only [pow_one] at h
    exact supportedBelow_mono h (by omega)
  · exact supportedBelow_Xpow hp 2

theorem pack_supportedBelow {N m : ℕ} (c : Fin N → Fin m → F2) (i : Fin N) :
    supportedBelow m (pack N m c i) := by
  classical
  intro k hk
  change (∑ j : Fin m, monomial j.val (c i j)).coeff k = 0
  simp only [finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by have := j.isLt; omega)]

theorem entry_pack_supportedBelow {N m : ℕ} (c : Fin N → Fin m → F2) (k : ℕ) :
    supportedBelow m (entry (pack N m c) k) := by
  unfold entry
  split
  · exact pack_supportedBelow c _
  · intro j _
    simp

/-- No X output is lost by restricting the transverse coordinate to `Fin (m + 2)`. -/
theorem xChecks_supportedBelow {n m : ℕ} (c : Fin (n + 2) → Fin m → F2)
    (i : Fin n) : supportedBelow (m + 2) (xChecks n m c i).1 ∧
      supportedBelow (m + 2) (xChecks n m c i).2 := by
  change supportedBelow (m + 2)
      (entry (pack (n + 2) m c) i + entry (pack (n + 2) m c) (i.val + 1) +
        (X : P) ^ 2 * entry (pack (n + 2) m c) (i.val + 2)) ∧
    supportedBelow (m + 2)
      (((X : P) + X ^ 2) * entry (pack (n + 2) m c) i +
        entry (pack (n + 2) m c) (i.val + 2))
  have hc (k : ℕ) := entry_pack_supportedBelow c k
  have hb (k : ℕ) : supportedBelow (m + 2) (entry (pack (n + 2) m c) k) :=
    supportedBelow_mono (hc k) (by omega)
  exact ⟨supportedBelow_add (supportedBelow_add (hb _) (hb _))
    (supportedBelow_Xpow (hc _) 2),
    supportedBelow_add (supportedBelow_transverse (hc _)) (hb _)⟩

/-- The reflected Z output also has no discarded transverse coefficients. -/
theorem zChecks_supportedBelow {n m : ℕ} (c : Fin (n + 2) → Fin m → F2)
    (i : Fin n) : supportedBelow (m + 2) (zChecks n m c i).1 ∧
      supportedBelow (m + 2) (zChecks n m c i).2 := by
  change supportedBelow (m + 2)
      (entry (pack (n + 2) m c) i +
        ((X : P) + X ^ 2) * entry (pack (n + 2) m c) (i.val + 2)) ∧
    supportedBelow (m + 2)
      (entry (pack (n + 2) m c) (i.val + 2) +
        (X : P) ^ 2 * entry (pack (n + 2) m c) (i.val + 1) +
        (X : P) ^ 2 * entry (pack (n + 2) m c) i)
  have hc (k : ℕ) := entry_pack_supportedBelow c k
  have hb (k : ℕ) : supportedBelow (m + 2) (entry (pack (n + 2) m c) k) :=
    supportedBelow_mono (hc k) (by omega)
  exact ⟨supportedBelow_add (hb _) (supportedBelow_transverse (hc _)),
    supportedBelow_add (supportedBelow_add (hb _) (supportedBelow_Xpow (hc _) 2))
      (supportedBelow_Xpow (hc _) 2)⟩

/-- Restriction to a finite rectangle of physical coefficients, retaining both blocks. -/
noncomputable def physicalProjection (n b : ℕ) :
    (Fin n → P × P) →ₗ[F2] (Fin n → Fin b → F2 × F2) where
  toFun v i j := ((v i).1.coeff j.val, (v i).2.coeff j.val)
  map_add' v w := by
    ext i j <;> simp
  map_smul' r v := by
    ext i j <;> simp

/-- Finite coefficient restriction is faithful on arrays supported in the rectangle. -/
theorem physicalProjection_eq_zero {n b : ℕ} (v : Fin n → P × P)
    (hb : ∀ i, supportedBelow b (v i).1 ∧ supportedBelow b (v i).2)
    (hv : physicalProjection n b v = 0) : v = 0 := by
  funext i
  apply Prod.ext
  · apply Polynomial.ext
    intro k
    by_cases hk : k < b
    · have h := congrArg (fun w : Fin n → Fin b → F2 × F2 => (w i ⟨k, hk⟩).1) hv
      simpa [physicalProjection] using h
    · simpa using (hb i).1 k (by omega)
  · apply Polynomial.ext
    intro k
    by_cases hk : k < b
    · have h := congrArg (fun w : Fin n → Fin b → F2 × F2 => (w i ⟨k, hk⟩).2) hv
      simpa [physicalProjection] using h
    · simpa using (hb i).2 k (by omega)

/-- Actual finite X check synthesis, with one pair of block values per physical cell. -/
noncomputable def xPhysical (n m : ℕ) :
    (Fin (n + 2) → Fin m → F2) →ₗ[F2] (Fin n → Fin (m + 2) → F2 × F2) :=
  (physicalProjection n (m + 2)).comp (xChecks n m)

/-- Actual finite reflected Z check synthesis (directional coordinate first). -/
noncomputable def zPhysical (n m : ℕ) :
    (Fin (n + 2) → Fin m → F2) →ₗ[F2] (Fin n → Fin (m + 2) → F2 × F2) :=
  (physicalProjection n (m + 2)).comp (zChecks n m)

theorem xPhysical_injective {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Function.Injective (xPhysical n m) := by
  suffices hz : ∀ c, xPhysical n m c = 0 → c = 0 by
    intro c d h
    have he : xPhysical n m (c - d) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hz (c - d) he)
  intro c h
  have hz := physicalProjection_eq_zero (xChecks n m c) (xChecks_supportedBelow c) h
  apply xChecks_injective hn m
  simpa using hz

theorem zPhysical_injective {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Function.Injective (zPhysical n m) := by
  suffices hz : ∀ c, zPhysical n m c = 0 → c = 0 by
    intro c d h
    have he : zPhysical n m (c - d) = 0 := by rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hz (c - d) he)
  intro c h
  have hz := physicalProjection_eq_zero (zChecks n m c) (zChecks_supportedBelow c) h
  apply zChecks_injective hn m
  simpa using hz

theorem xPhysical_finrank {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Module.finrank F2 (LinearMap.range (xPhysical n m)) = (n + 2) * m := by
  rw [LinearMap.finrank_range_of_inj (xPhysical_injective hn m)]
  simp [Module.finrank_pi_fintype]

theorem zPhysical_finrank {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    Module.finrank F2 (LinearMap.range (zPhysical n m)) = (n + 2) * m := by
  rw [LinearMap.finrank_range_of_inj (zPhysical_injective hn m)]
  simp [Module.finrank_pi_fintype]

/-- Both explicit 722-coordinate synthesis maps have independent 357-element domains. -/
theorem physical722_injective :
    Function.Injective (xPhysical 19 17) ∧ Function.Injective (zPhysical 19 17) :=
  ⟨xPhysical_injective (by omega) 17, zPhysical_injective (by omega) 17⟩

/-- Rank 357 for each explicit finite directional check map, by algebra alone. -/
theorem physical722_rank :
    Module.finrank F2 (LinearMap.range (xPhysical 19 17)) = 357 ∧
    Module.finrank F2 (LinearMap.range (zPhysical 19 17)) = 357 := by
  constructor
  · exact xPhysical_finrank (by omega) 17
  · exact zPhysical_finrank (by omega) 17

/-- X synthesis with the original anchor and physical coordinate types. -/
noncomputable def xSynthesis : (XAnchor → F2) →ₗ[F2] (PhysicalQ → F2) :=
  xPhysicalCoordinates.toLinearMap.comp
    ((xPhysical 19 17).comp xAnchorCoordinates.toLinearMap)

/-- Z synthesis with original coordinates; all reflection permutations are explicit. -/
noncomputable def zSynthesis : (ZAnchor → F2) →ₗ[F2] (PhysicalQ → F2) :=
  zPhysicalCoordinates.toLinearMap.comp
    ((zPhysical 19 17).comp zAnchorCoordinates.toLinearMap)

theorem xSynthesis_injective : Function.Injective xSynthesis :=
  xPhysicalCoordinates.injective.comp
    (physical722_injective.1.comp xAnchorCoordinates.injective)

theorem zSynthesis_injective : Function.Injective zSynthesis :=
  zPhysicalCoordinates.injective.comp
    (physical722_injective.2.comp zAnchorCoordinates.injective)

theorem xSynthesis_rank : Module.finrank F2 (LinearMap.range xSynthesis) = 357 := by
  rw [LinearMap.finrank_range_of_inj xSynthesis_injective]
  simp [XAnchor]

theorem zSynthesis_rank : Module.finrank F2 (LinearMap.range zSynthesis) = 357 := by
  rw [LinearMap.finrank_range_of_inj zSynthesis_injective]
  simp [ZAnchor]

end QldpcVerification.Planar.BoundaryRecurrence
