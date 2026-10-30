import QldpcVerification.QubitRemoval
import QldpcVerification.Input.SparseCertificates

/-! Physical permutations, row permutations, and reversible stabilizer-row clearing.
These operations preserve the actual logical predicates and physical Hamming weight. -/
namespace QldpcVerification.QubitRemovalTransport
open Matrix Module Input

variable {n mX mZ : ℕ}

/-- Exchange X and Z without changing physical coordinates. -/
def dual (C : CSSCode n mX mZ) : CSSCode n mZ mX where
  HX := C.HZ
  HZ := C.HX
  comm := by
    have h := congrArg Matrix.transpose C.comm
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] using h

@[simp] theorem dual_x (C : CSSCode n mX mZ) (x : Vec n) :
    (dual C).IsXLogical x ↔ C.IsZLogical x := Iff.rfl
@[simp] theorem dual_z (C : CSSCode n mX mZ) (x : Vec n) :
    (dual C).IsZLogical x ↔ C.IsXLogical x := Iff.rfl
@[simp] theorem dual_xStab (C : CSSCode n mX mZ) : (dual C).xStab = C.zStab := rfl
@[simp] theorem dual_zStab (C : CSSCode n mX mZ) : (dual C).zStab = C.xStab := rfl

/-- Pull a physical vector along a permutation of the qubit coordinates. -/
def perm (e : Fin n ≃ Fin n) : Vec n ≃ₗ[ZMod 2] Vec n where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by ext i; simp [Function.comp_def]
  right_inv x := by ext i; simp [Function.comp_def]
  map_add' x y := rfl
  map_smul' a x := rfl

@[simp] theorem perm_dot (e : Fin n ≃ Fin n) (x y : Vec n) :
    perm e x ⬝ᵥ perm e y = x ⬝ᵥ y := by
  exact Equiv.sum_comp e (fun i => x i * y i)

@[simp] theorem perm_weight (e : Fin n ≃ Fin n) (x : Vec n) :
    hammingNorm (perm e x) = hammingNorm x := by
  classical
  simp only [hammingNorm, Finset.card_filter]
  exact Equiv.sum_comp e (fun i => if x i ≠ 0 then 1 else 0)

/-- Coordinate and check-row permutations. All maps go from the new labels to old labels. -/
def relabel (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) : CSSCode n mX mZ where
  HX i := perm e (C.HX (rX i))
  HZ i := perm e (C.HZ (rZ i))
  comm := by
    ext i j
    change perm e (C.HX (rX i)) ⬝ᵥ perm e (C.HZ (rZ j)) = 0
    rw [perm_dot]
    exact congrFun (congrFun C.comm (rX i)) (rZ j)

theorem relabel_xStab (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) :
    (relabel C e rX rZ).xStab = C.xStab.map (perm e).toLinearMap := by
  rw [CSSCode.xStab, CSSCode.xStab, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨_, ⟨rX i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨rX.symm i, by simp [relabel]⟩

theorem relabel_zStab (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) :
    (relabel C e rX rZ).zStab = C.zStab.map (perm e).toLinearMap := by
  exact relabel_xStab (dual C) e rZ rX

@[simp] theorem perm_mem_map (e : Fin n ≃ Fin n) (S : Submodule (ZMod 2) (Vec n))
    (x : Vec n) : perm e x ∈ S.map (perm e).toLinearMap ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, he⟩; exact (perm e).injective he ▸ hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem relabel_X (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) (x : Vec n) :
    (relabel C e rX rZ).IsXLogical (perm e x) ↔ C.IsXLogical x := by
  rw [CSSCode.IsXLogical, CSSCode.IsXLogical, relabel_xStab, perm_mem_map]
  have hc : (relabel C e rX rZ).HZ.mulVec (perm e x) = 0 ↔ C.HZ.mulVec x = 0 := by
    simp only [funext_iff, Matrix.mulVec, Pi.zero_apply]
    constructor
    · intro h j
      simpa [relabel] using h (rZ.symm j)
    · intro h j
      simpa [relabel] using h (rZ j)
  rw [hc]

theorem relabel_Z (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) (x : Vec n) :
    (relabel C e rX rZ).IsZLogical (perm e x) ↔ C.IsZLogical x :=
  relabel_X (dual C) e rZ rX x

theorem relabel_rankX (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) :
    finrank (ZMod 2) (relabel C e rX rZ).xStab = finrank (ZMod 2) C.xStab := by
  rw [relabel_xStab]
  exact LinearEquiv.finrank_map_eq (perm e) _

theorem relabel_rankZ (C : CSSCode n mX mZ) (e : Fin n ≃ Fin n)
    (rX : Fin mX ≃ Fin mX) (rZ : Fin mZ ≃ Fin mZ) :
    finrank (ZMod 2) (relabel C e rX rZ).zStab = finrank (ZMod 2) C.zStab :=
  relabel_rankX (dual C) e rZ rX

/-- Add a multiple of a distinguished X check to the other X checks.
The distinguished row is fixed, making this operation its own inverse over F₂. -/
def shearX (C : CSSCode n mX mZ) (p : Fin mX) (c : Fin mX → ZMod 2)
    (hc : c p = 0) : CSSCode n mX mZ where
  HX i := C.HX i + c i • C.HX p
  HZ := C.HZ
  comm := by
    ext i j
    change (C.HX i + c i • C.HX p) ⬝ᵥ C.HZ j = 0
    rw [add_dotProduct, smul_dotProduct]
    have hi := congrFun (congrFun C.comm i) j
    have hp := congrFun (congrFun C.comm p) j
    change C.HX i ⬝ᵥ C.HZ j = 0 at hi
    change C.HX p ⬝ᵥ C.HZ j = 0 at hp
    simp [hi, hp]

theorem shearX_xStab (C : CSSCode n mX mZ) (p : Fin mX) (c : Fin mX → ZMod 2)
    (hc : c p = 0) : (shearX C p c hc).xStab = C.xStab := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact C.xStab.add_mem (Submodule.subset_span ⟨i, rfl⟩)
      (C.xStab.smul_mem _ (Submodule.subset_span ⟨p, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hp : C.HX p ∈ (shearX C p c hc).xStab := by
      simpa [shearX, hc] using
        (Submodule.subset_span ⟨p, rfl⟩ : (shearX C p c hc).HX p ∈ (shearX C p c hc).xStab)
    have hi : (shearX C p c hc).HX i ∈ (shearX C p c hc).xStab :=
      Submodule.subset_span ⟨i, rfl⟩
    have h := (shearX C p c hc).xStab.sub_mem hi
      ((shearX C p c hc).xStab.smul_mem (c i) hp)
    simpa [shearX] using h

@[simp] theorem shearX_X (C : CSSCode n mX mZ) (p : Fin mX)
    (c : Fin mX → ZMod 2) (hc : c p = 0) (x : Vec n) :
    (shearX C p c hc).IsXLogical x ↔ C.IsXLogical x := by
  simp only [CSSCode.IsXLogical, shearX_xStab]; rfl

@[simp] theorem shearX_Z (C : CSSCode n mX mZ) (p : Fin mX)
    (c : Fin mX → ZMod 2) (hc : c p = 0) (z : Vec n) :
    (shearX C p c hc).IsZLogical z ↔ C.IsZLogical z := by
  change ((shearX C p c hc).HX.mulVec z = 0 ∧ z ∉ C.zStab) ↔ _
  have hz : (shearX C p c hc).HX.mulVec z = 0 ↔ C.HX.mulVec z = 0 := by
    simp only [funext_iff, Matrix.mulVec, Pi.zero_apply]
    constructor
    · intro h i
      have hp : C.HX p ⬝ᵥ z = 0 := by simpa [shearX, hc] using h p
      have hi := h i
      change (C.HX i + c i • C.HX p) ⬝ᵥ z = 0 at hi
      simpa [add_dotProduct, smul_dotProduct, hp] using hi
    · intro h i
      change (C.HX i + c i • C.HX p) ⬝ᵥ z = 0
      rw [add_dotProduct, smul_dotProduct, h i, h p]; simp
  rw [hz]; rfl

end QldpcVerification.QubitRemovalTransport

namespace QldpcVerification.QubitRemovalTransport
open Matrix Module Input Input.Sparse QubitRemoval
variable {n mX mZ : ℕ}

/-- A certified elementary extension, including reversible same-type row clearing. -/
def extension (C : CSSCode n mX mZ) (s : Vec n)
    (c : Fin (mX + 1) → ZMod 2) (hc : c (Fin.last mX) = 0)
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (rX : Fin (mX + 1) ≃ Fin (mX + 1)) (rZ : Fin mZ ≃ Fin mZ) :
    CSSCode (n + 1) (mX + 1) mZ :=
  relabel (shearX (old C s) (Fin.last mX) c hc) e rX rZ

variable (C : CSSCode n mX mZ) (s : Vec n)
    (c : Fin (mX + 1) → ZMod 2) (hc : c (Fin.last mX) = 0)
    (e : Fin (n + 1) ≃ Fin (n + 1))
    (rX : Fin (mX + 1) ≃ Fin (mX + 1)) (rZ : Fin mZ ≃ Fin mZ)

@[simp] theorem extension_X (x : Vec (n + 1)) :
    (extension C s c hc e rX rZ).IsXLogical (perm e x) ↔ (old C s).IsXLogical x := by
  rw [extension, relabel_X, shearX_X]
@[simp] theorem extension_Z (z : Vec (n + 1)) :
    (extension C s c hc e rX rZ).IsZLogical (perm e z) ↔ (old C s).IsZLogical z := by
  rw [extension, relabel_Z, shearX_Z]

theorem extension_rankX :
    finrank (ZMod 2) (extension C s c hc e rX rZ).xStab =
      finrank (ZMod 2) C.xStab + 1 := by
  rw [extension, relabel_rankX, shearX_xStab, QubitRemoval.rankX]

theorem extension_rankZ :
    finrank (ZMod 2) (extension C s c hc e rX rZ).zStab =
      finrank (ZMod 2) C.zStab := by
  rw [extension, relabel_rankZ]
  exact QubitRemoval.rankZ C s

theorem extension_new_X_lower {D : ℕ}
    (h : ∀ y, (extension C s c hc e rX rZ).IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, C.IsXLogical x → D ≤ hammingNorm x := by
  apply QubitRemoval.new_X_lower C s
  intro y hy
  simpa using h (perm e y) ((extension_X C s c hc e rX rZ y).mpr hy)

theorem extension_new_Z_lower {D : ℕ}
    (h : ∀ y, (extension C s c hc e rX rZ).IsZLogical y → D ≤ hammingNorm y) :
    ∀ x, C.IsZLogical x → D - 1 ≤ hammingNorm x := by
  apply QubitRemoval.new_Z_lower C s
  intro y hy
  simpa using h (perm e y) ((extension_Z C s c hc e rX rZ y).mpr hy)

/-- A zero fan is a decoupled stabilizer qubit; it costs no distance on either side. -/
theorem extension_zero_new_Z_lower {D : ℕ}
    (h : ∀ y, (extension C 0 c hc e rX rZ).IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, C.IsZLogical z → D ≤ hammingNorm z := by
  intro z hz
  have hy := (QubitRemoval.liftZ_logical_iff C 0 z).mpr hz
  have hl := h _ ((extension_Z C 0 c hc e rX rZ _).mpr hy)
  simpa [QubitRemoval.liftZ_weight, QubitRemoval.bitWeight] using hl

/-- Extensionality for literal matrix recognition, including the commutation proof. -/
theorem code_eq {C D : CSSCode n mX mZ} (hx : C.HX = D.HX) (hz : C.HZ = D.HZ) : C = D := by
  cases C; cases D; cases hx; cases hz; rfl

end QldpcVerification.QubitRemovalTransport

namespace QldpcVerification.QubitRemovalTransport
open Input
@[simp] theorem dual_dual {n mX mZ : ℕ} (C : CSSCode n mX mZ) : dual (dual C) = C := by
  cases C; rfl
end QldpcVerification.QubitRemovalTransport
