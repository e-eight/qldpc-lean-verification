import QldpcVerification.Input.SparseCertificates
import QEC.Stabilizer.Framework.Homological.F2Mask
import Mathlib.Data.Finset.Fold

/-! Sparse row-combination certificates evaluated with packed XOR.
The checker proves actual stabilizer membership, not merely zero syndrome. -/

namespace QldpcVerification.Distance566Certificates

open Matrix Input Input.Sparse Quantum.Stabilizer.Homological

set_option maxHeartbeats 0

theorem vec_xor {n : ℕ} (a b : ℕ) : vec n (a ^^^ b) = vec n a + vec n b := by
  ext q
  change (if bit (a ^^^ b) q then (1 : ZMod 2) else 0) =
    (if bit a q then 1 else 0) + (if bit b q then 1 else 0)
  simp only [bit, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_xor]
  cases ha : a.testBit q <;> cases hb : b.testBit q <;> simp [ha, hb] <;> decide

theorem vec_xorList {n : ℕ} (l : List ℕ) :
    vec n (F2Mask.xorList l) = (l.map (vec n)).sum := by
  induction l with
  | nil => ext q; simp [F2Mask.xorList, vec, bit]
  | cons a l ih => simp only [F2Mask.xorList_cons, List.map_cons, List.sum_cons, vec_xor, ih]

theorem vec_single {n : ℕ} (q : Fin n) : vec n (2 ^ (q : ℕ)) = Pi.single q 1 := by
  ext j
  simp only [vec, bit, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_two_pow,
    Pi.single_apply]
  simp [Fin.ext_iff, eq_comm]

local instance : Std.Commutative Nat.xor := ⟨Nat.xor_comm⟩
local instance : Std.Associative Nat.xor := ⟨Nat.xor_assoc⟩

def supportMask {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  s.fold Nat.xor 0 fun q => 2 ^ q.val

theorem supportMask_insert {n : ℕ} (q : Fin n) (s : Finset (Fin n)) (h : q ∉ s) :
    supportMask (insert q s) = 2 ^ q.val ^^^ supportMask s :=
  Finset.fold_insert h

theorem vec_supportMask {n : ℕ} (s : Finset (Fin n)) :
    vec n (supportMask s) = indicator s := by
  induction s using Finset.induction_on with
  | empty => ext q; simp [supportMask, vec, bit, indicator]
  | @insert a s ha ih =>
    rw [supportMask_insert a s ha, vec_xor, vec_single, ih]
    ext q
    by_cases hq : q = a
    · subst q; simp [indicator, ha]
    · simp [indicator, hq, Ne.symm hq, Pi.single_apply]

def rowCheck {n : ℕ} (rows : List (Finset (Fin n))) (base representative : ℕ)
    (indices : List (Fin rows.length)) : Bool :=
  representative == (base ^^^ F2Mask.xorList (indices.map fun i => supportMask (rows.get i)))

theorem rowCheck_sound {n : ℕ} (rows : List (Finset (Fin n))) (base representative : ℕ)
    (indices : List (Fin rows.length)) (h : rowCheck rows base representative indices = true) :
    vec n representative - vec n base ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
  have he : representative = base ^^^
      F2Mask.xorList (indices.map fun i => supportMask (rows.get i)) := beq_iff_eq.mp h
  rw [he, vec_xor, vec_xorList]
  have hs : ((indices.map fun i => supportMask (rows.get i)).map (vec n)).sum ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
    clear h he
    induction indices with
    | nil => simpa using (Submodule.zero_mem (Submodule.span (ZMod 2) (Set.range (matrix rows))))
    | cons i indices ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Submodule.add_mem _ _ ih
      rw [vec_supportMask]
      exact Submodule.subset_span ⟨i, rfl⟩
  simpa only [add_sub_cancel_left] using hs

def classCheck {n : ℕ} (rows : List (Finset (Fin n))) (base : ℕ)
    (reps : List (ℕ × List (Fin rows.length))) : Bool :=
  reps.all fun r => rowCheck rows base r.1 r.2

theorem classCheck_sound {n : ℕ} (rows : List (Finset (Fin n))) (base : ℕ)
    (reps : List (ℕ × List (Fin rows.length))) (h : classCheck rows base reps = true)
    (i : Fin reps.length) : vec n (reps.get i).1 - vec n base ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) :=
  rowCheck_sound rows base _ _ (List.all_eq_true.mp h _ (List.get_mem reps i))

theorem classCheck_map_sound {n : ℕ} (rows : List (Finset (Fin n))) (base : ℕ)
    (reps : List (ℕ × List (Fin rows.length))) (h : classCheck rows base reps = true)
    (i : Fin (reps.map (fun r => (r.1, (1 : ℕ)))).length) :
    vec n ((reps.map (fun r => (r.1, (1 : ℕ)))).get i).1 - vec n base ∈
      Submodule.span (ZMod 2) (Set.range (matrix rows)) := by
  have hi : (i : ℕ) < reps.length := by simpa only [List.length_map] using i.isLt
  simpa only [List.get_eq_getElem, List.getElem_map] using
    classCheck_sound rows base reps h ⟨i, hi⟩

end QldpcVerification.Distance566Certificates
