import QldpcCert.Bits
import QldpcCert.Surface225Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 100
open Bits Surface225
namespace KernelChunks

theorem allOf_append (p : Nat → Bool) (xs ys : List Nat) :
    allOf p (xs ++ ys) = (allOf p xs && allOf p ys) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, allOf, ih, Bool.and_assoc]

theorem allOf_split (p : Nat → Bool) (xs : List Nat) (k : Nat)
    (h₁ : allOf p (xs.take k) = true) (h₂ : allOf p (xs.drop k) = true) :
    allOf p xs = true := by
  have h := congrArg (allOf p) (List.take_append_drop k xs)
  rw [allOf_append, h₁, h₂] at h
  exact h.symm

theorem comm : commCheck nq 8 hx hz = true := by
  unfold commCheck
  apply allOf_split _ _ 16
  · decide +kernel
  apply allOf_split _ _ 16
  · decide +kernel
  apply allOf_split _ _ 16
  · decide +kernel
  apply allOf_split _ _ 16
  · decide +kernel
  apply allOf_split _ _ 16
  · decide +kernel
  apply allOf_split _ _ 16
  · decide +kernel
  decide +kernel
#print axioms comm
end KernelChunks
