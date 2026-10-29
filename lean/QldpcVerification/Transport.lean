import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-! Reindexing preserves the matrix specification's logical spaces and weights. -/

namespace QldpcVerification

open Matrix

variable {Q V R S : Type} [Fintype Q] [Fintype V] [Fintype R] [Fintype S]

/-- Pull a vector back along a bijection of qubits. -/
def pull (e : V ≃ Q) : (Q → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by funext q; simp
  right_inv x := by funext v; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_dot (e : V ≃ Q) (x y : Q → ZMod 2) :
    pull e x ⬝ᵥ pull e y = x ⬝ᵥ y := by
  exact e.sum_comp (fun q => x q * y q)

theorem pull_weight (e : V ≃ Q) (x : Q → ZMod 2) :
    hammingNorm (pull e x) = hammingNorm x := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact e.sum_comp (fun q => if x q ≠ 0 then 1 else 0)

omit [Fintype Q] [Fintype V] [Fintype R] [Fintype S] in
/-- Row labels can be reordered or repeated, provided every target row occurs. -/
theorem rowspace_pull (e : V ≃ Q)
    (M : Matrix R Q (ZMod 2)) (N : Matrix S V (ZMod 2))
    (f : R → S) (hf : Function.Surjective f)
    (hrows : ∀ i, pull e (M i) = N (f i)) :
    Submodule.map (pull e).toLinearMap (Submodule.span (ZMod 2) (Set.range M)) =
      Submodule.span (ZMod 2) (Set.range N) := by
  have hr : (pull e) '' Set.range M = Set.range N := by
    ext v
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨f i, (hrows i).symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨i, rfl⟩ := hf j
      exact ⟨M i, ⟨i, rfl⟩, hrows i⟩
  rw [Submodule.map_span]
  exact congrArg (Submodule.span (ZMod 2)) hr

omit [Fintype Q] [Fintype V] [Fintype R] [Fintype S] in
theorem rowspace_pull_iff (e : V ≃ Q)
    (M : Matrix R Q (ZMod 2)) (N : Matrix S V (ZMod 2))
    (f : R → S) (hf : Function.Surjective f)
    (hrows : ∀ i, pull e (M i) = N (f i)) (x : Q → ZMod 2) :
    pull e x ∈ Submodule.span (ZMod 2) (Set.range N) ↔
      x ∈ Submodule.span (ZMod 2) (Set.range M) := by
  rw [← rowspace_pull e M N f hf hrows]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (pull e).injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Fintype R] [Fintype S] in
theorem kernel_pull_iff (e : V ≃ Q)
    (M : Matrix R Q (ZMod 2)) (N : Matrix S V (ZMod 2))
    (f : R → S) (hf : Function.Surjective f)
    (hrows : ∀ i, pull e (M i) = N (f i)) (x : Q → ZMod 2) :
    N.mulVec (pull e x) = 0 ↔ M.mulVec x = 0 := by
  have hd (i : R) : N (f i) ⬝ᵥ pull e x = M i ⬝ᵥ x := by
    rw [← hrows i, pull_dot]
  constructor
  · intro h
    funext i
    exact (hd i).symm.trans (congrFun h (f i))
  · intro h
    funext j
    obtain ⟨i, rfl⟩ := hf j
    exact (hd i).trans (congrFun h i)

end QldpcVerification
