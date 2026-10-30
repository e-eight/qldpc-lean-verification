import QldpcVerification.QubitRemovalTransport
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.SymmDiff

/-! Sparse, kernel-checkable recognition of one physical removal step.
The lists are literal physical supports. No distance search is involved. -/
namespace QldpcVerification.QubitRemovalSequence
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport
open scoped symmDiff

/-- Move a selected coordinate to the end, preserving all retained coordinates' order. -/
def moveLast {n : ℕ} (q : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquiv' q).trans (finSuccEquiv' (Fin.last n)).symm

def castSupport {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  s.map ⟨Fin.castSucc, Fin.castSucc_injective _⟩

def snocSupport {n : ℕ} (s : Finset (Fin n)) (b : Bool) : Finset (Fin (n + 1)) :=
  castSupport s ∪ if b then {Fin.last n} else ∅

def graphSupport {n : ℕ} (fan s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  snocSupport s (decide ((fan ∩ s).card % 2 = 1))

@[simp] theorem indicator_cast {n : ℕ} (s : Finset (Fin n)) :
    indicator (castSupport s) = pad (indicator s) := by
  ext q
  refine Fin.lastCases ?_ (fun j => ?_) q <;> simp [indicator, castSupport, pad]

@[simp] theorem indicator_snoc {n : ℕ} (s : Finset (Fin n)) (b : Bool) :
    indicator (snocSupport s b) = Fin.snoc (indicator s) (if b then 1 else 0) := by
  ext q
  refine Fin.lastCases ?_ (fun j => ?_) q <;> cases b <;>
    simp [indicator, snocSupport, castSupport]

@[simp] theorem indicator_graph {n : ℕ} (s fan : Finset (Fin n)) :
    indicator (graphSupport fan s) = liftZ (indicator fan) (indicator s) := by
  rw [graphSupport, indicator_snoc]
  ext q
  refine Fin.lastCases ?_ (fun j => ?_) q
  · simp only [liftZ, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_last]
    change (if decide ((fan ∩ s).card % 2 = 1) then (1 : ZMod 2) else 0) =
      indicator fan ⬝ᵥ indicator s
    rw [indicator_dot_indicator, ← ZMod.natCast_mod _ 2]
    have h : (fan ∩ s).card % 2 = 0 ∨ (fan ∩ s).card % 2 = 1 := by omega
    rcases h with h | h <;> simp [h]
  · simp [liftZ]

@[simp] theorem indicator_empty {n : ℕ} : indicator (∅ : Finset (Fin n)) = 0 := by
  ext q; simp [indicator]

@[simp] theorem indicator_map {n : ℕ} (s : Finset (Fin n)) (e : Fin n ≃ Fin n) :
    indicator (s.map e.symm.toEmbedding) = perm e (indicator s) := by
  ext q
  simp [indicator, perm, Function.comp_def]

@[simp] theorem indicator_xor {n : ℕ} (s t : Finset (Fin n)) :
    indicator (s ∆ t) = indicator s + indicator t := by
  ext q
  by_cases hs : q ∈ s <;> by_cases ht : q ∈ t <;>
    simp [indicator, Finset.mem_symmDiff, hs, ht, CharTwo.add_self_eq_zero]

/-- Normalized same-type supports, with an optional reversible row shear. -/
def normalX {n : ℕ} (xs : List (Finset (Fin n))) (fan : Finset (Fin n))
    (clear : Finset (Fin (xs.length + 1))) (i : Fin (xs.length + 1)) :
    Finset (Fin (n + 1)) :=
  (Fin.snoc (fun j : Fin xs.length => castSupport (xs.get j)) (snocSupport fan true) :
    Fin (xs.length + 1) → Finset (Fin (n + 1))) i ∆
    (if i ∈ clear then snocSupport fan true else ∅)

def normalZ {n : ℕ} (zs : List (Finset (Fin n))) (fan : Finset (Fin n))
    (i : Fin zs.length) : Finset (Fin (n + 1)) := graphSupport fan (zs.get i)

variable {n : ℕ} (xs zs : List (Finset (Fin n))) (fan : Finset (Fin n))
    (clear : Finset (Fin (xs.length + 1))) (hc : Fin.last xs.length ∉ clear)
    (C : CSSCode n xs.length zs.length) (hx : C.HX = matrix xs) (hz : C.HZ = matrix zs)

include hc in
private theorem clear_zero : indicator clear (Fin.last xs.length) = 0 := by
  simp [indicator, hc]

include hx in
/-- Vector interpretation of the normalized same-type finite supports. -/
theorem normalX_indicator (i : Fin (xs.length + 1)) :
    indicator (normalX xs fan clear i) =
      (shearX (old C (indicator fan)) (Fin.last xs.length) (indicator clear)
        (clear_zero xs clear hc)).HX i := by
  rw [normalX, indicator_xor]
  change _ = (old C (indicator fan)).HX i + indicator clear i •
    (old C (indicator fan)).HX (Fin.last xs.length)
  congr 1
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [old]
    · simp [old, hx, matrix]
  · by_cases hi : i ∈ clear <;> simp [hi, indicator, old]

include hz in
/-- Vector interpretation of the normalized opposite-type finite supports. -/
theorem normalZ_indicator (i : Fin zs.length) :
    indicator (normalZ zs fan i) = (old C (indicator fan)).HZ i := by
  simp [normalZ, old, hz, matrix]

/-- Finite support equalities recognize literal physical matrices as one legal step. -/
def recognize
    (beforeX : Fin (xs.length + 1) → Finset (Fin (n + 1)))
    (beforeZ : Fin zs.length → Finset (Fin (n + 1)))
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (rX : Fin (xs.length + 1) ≃ Fin (xs.length + 1))
    (rZ : Fin zs.length ≃ Fin zs.length)
    (checkX : ∀ i, beforeX i = (normalX xs fan clear (rX i)).map e.symm.toEmbedding)
    (checkZ : ∀ i, beforeZ i = (normalZ zs fan (rZ i)).map e.symm.toEmbedding) :
    CSSCode (n + 1) (xs.length + 1) zs.length where
  HX i := indicator (beforeX i)
  HZ i := indicator (beforeZ i)
  comm := by
    ext i j
    change indicator (beforeX i) ⬝ᵥ indicator (beforeZ j) = 0
    rw [checkX i, checkZ j, indicator_map, indicator_map, perm_dot]
    rw [normalX_indicator xs zs fan clear hc C hx, normalZ_indicator xs zs fan C hz]
    exact congrFun (congrFun
      (shearX (old C (indicator fan)) (Fin.last xs.length) (indicator clear)
        (clear_zero xs clear hc)).comm (rX i)) (rZ j)

/-- Recognition is equality of physical CSS codes, not only an abstract parameter match. -/
theorem recognize_eq
    (beforeX : Fin (xs.length + 1) → Finset (Fin (n + 1)))
    (beforeZ : Fin zs.length → Finset (Fin (n + 1)))
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (rX : Fin (xs.length + 1) ≃ Fin (xs.length + 1))
    (rZ : Fin zs.length ≃ Fin zs.length)
    (checkX : ∀ i, beforeX i = (normalX xs fan clear (rX i)).map e.symm.toEmbedding)
    (checkZ : ∀ i, beforeZ i = (normalZ zs fan (rZ i)).map e.symm.toEmbedding) :
    recognize xs zs fan clear hc C hx hz beforeX beforeZ e rX rZ checkX checkZ =
      extension C (indicator fan) (indicator clear) (clear_zero xs clear hc) e rX rZ := by
  apply code_eq
  · ext i q
    change indicator (beforeX i) q = perm e
      ((shearX (old C (indicator fan)) (Fin.last xs.length) (indicator clear)
        (clear_zero xs clear hc)).HX (rX i)) q
    rw [checkX i, indicator_map, normalX_indicator xs zs fan clear hc C hx]
  · ext i q
    change indicator (beforeZ i) q = perm e ((old C (indicator fan)).HZ (rZ i)) q
    rw [checkZ i, indicator_map, normalZ_indicator xs zs fan C hz]

end QldpcVerification.QubitRemovalSequence

namespace QldpcVerification.QubitRemovalSequence
open Input.Sparse
/-- Split finite checking into bounded blocks without weakening the checked proposition. -/
theorem commCheck_append {n : ℕ} (xs ys zs : List (Finset (Fin n))) :
    commCheck (xs ++ ys) zs = (commCheck xs zs && commCheck ys zs) := by
  simp [commCheck, List.all_append]

theorem allIdx_append {α : Type} (p : ℕ → α → Bool) (xs ys : List α) (k : ℕ) :
    allIdx p (xs ++ ys) k = (allIdx p xs k && allIdx p ys (k + xs.length)) := by
  induction xs generalizing k with
  | nil => simp [allIdx]
  | cons a xs ih => simp [allIdx, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
end QldpcVerification.QubitRemovalSequence

namespace QldpcVerification.QubitRemovalSequence
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport
variable {n : ℕ} (xs zs : List (Finset (Fin n))) (fan : Finset (Fin n))
    (clear : Finset (Fin (xs.length + 1))) (hc : Fin.last xs.length ∉ clear)
    (C : CSSCode n xs.length zs.length) (hx : C.HX = matrix xs) (hz : C.HZ = matrix zs)
    (beforeX : Fin (xs.length + 1) → Finset (Fin (n + 1)))
    (beforeZ : Fin zs.length → Finset (Fin (n + 1)))
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (rX : Fin (xs.length + 1) ≃ Fin (xs.length + 1)) (rZ : Fin zs.length ≃ Fin zs.length)
    (checkX : ∀ i, beforeX i = (normalX xs fan clear (rX i)).map e.symm.toEmbedding)
    (checkZ : ∀ i, beforeZ i = (normalZ zs fan (rZ i)).map e.symm.toEmbedding)

local notation "R" => recognize xs zs fan clear hc C hx hz beforeX beforeZ e rX rZ checkX checkZ

theorem recognize_rankX : finrank (ZMod 2) (R).xStab = finrank (ZMod 2) C.xStab + 1 := by
  rw [recognize_eq, extension_rankX]
theorem recognize_rankZ : finrank (ZMod 2) (R).zStab = finrank (ZMod 2) C.zStab := by
  rw [recognize_eq, extension_rankZ]

theorem recognize_new_X_lower {D : ℕ}
    (h : ∀ y, (R).IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, C.IsXLogical x → D ≤ hammingNorm x := by
  rw [recognize_eq] at h
  exact extension_new_X_lower _ _ _ _ _ _ _ h

theorem recognize_new_Z_lower {D : ℕ}
    (h : ∀ y, (R).IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, C.IsZLogical z → D - 1 ≤ hammingNorm z := by
  rw [recognize_eq] at h
  exact extension_new_Z_lower _ _ _ _ _ _ _ h

theorem recognize_zero_new_Z_lower (hf : indicator fan = 0) {D : ℕ}
    (h : ∀ y, (R).IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, C.IsZLogical z → D ≤ hammingNorm z := by
  rw [recognize_eq, hf] at h
  exact extension_zero_new_Z_lower _ _ _ _ _ _ h
end QldpcVerification.QubitRemovalSequence
