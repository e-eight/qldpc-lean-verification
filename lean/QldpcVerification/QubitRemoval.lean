import QldpcVerification.Input.Homological
import Mathlib.Algebra.CharP.Two

/-!
An elementary X-check removal in row-normalized CNOT coordinates.  The retained
code has checks A,B.  The old checks are (A,0),(s,1) and (B,Bs).  All weights below
refer to physical coordinates of these two matrices, before any further CNOTs.
-/
namespace QldpcVerification.QubitRemoval

open Matrix Module Input

variable {n mX mZ : ℕ}

@[simp] theorem snoc_dot (x y : Vec n) (a b : ZMod 2) :
    Fin.snoc x a ⬝ᵥ Fin.snoc y b = x ⬝ᵥ y + a * b := by
  simp [dotProduct, Fin.sum_univ_castSucc]

@[simp] theorem snoc_dot_any (x : Vec n) (a : ZMod 2) (y : Vec (n + 1)) :
    Fin.snoc x a ⬝ᵥ y = x ⬝ᵥ Fin.init y + a * y (Fin.last n) := by
  simp [dotProduct, Fin.sum_univ_castSucc, Fin.init]

/-- Append a zero physical coordinate. -/
def pad : Vec n →ₗ[ZMod 2] Vec (n + 1) where
  toFun x := Fin.snoc x 0
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Z lift: the discarded coordinate is forced by the distinguished X check. -/
def liftZ (s : Vec n) : Vec n →ₗ[ZMod 2] Vec (n + 1) where
  toFun z := Fin.snoc z (s ⬝ᵥ z)
  map_add' x y := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [dotProduct_add]
  map_smul' a x := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [dotProduct_smul]

/-- Decode X through the fan-out: subtract the last bit times s. -/
def decodeX (s : Vec n) : Vec (n + 1) →ₗ[ZMod 2] Vec n where
  toFun y := Fin.init y - y (Fin.last n) • s
  map_add' x y := by ext i; simp [Fin.init, add_smul]; ring
  map_smul' a x := by ext i; simp [Fin.init]; ring

/-- All old X representatives of x, including the distinguished stabilizer. -/
def liftX (s x : Vec n) (t : ZMod 2) : Vec (n + 1) := Fin.snoc (x + t • s) t

@[simp] theorem decode_liftX (s x : Vec n) (t : ZMod 2) :
    decodeX s (liftX s x t) = x := by
  simp [decodeX, liftX]

@[simp] theorem liftX_decode (s : Vec n) (y : Vec (n + 1)) :
    liftX s (decodeX s y) (y (Fin.last n)) = y := by
  simp [liftX, decodeX]

@[simp] theorem liftX_zero (s x : Vec n) : liftX s x 0 = pad x := by
  simp [liftX, pad]

/-- Concrete old CSS matrices; the retained matrices are exactly C.HX,C.HZ. -/
def old (C : CSSCode n mX mZ) (s : Vec n) : CSSCode (n + 1) (mX + 1) mZ where
  HX := Fin.snoc (fun i => pad (C.HX i)) (Fin.snoc s 1)
  HZ := fun j => liftZ s (C.HZ j)
  comm := by
    ext i j
    change _ ⬝ᵥ liftZ s (C.HZ j) = 0
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp [liftZ, CharTwo.add_self_eq_zero]
    · simpa [pad, liftZ] using congrFun (congrFun C.comm k) j

variable (C : CSSCode n mX mZ) (s : Vec n)

@[simp] theorem old_HX_castSucc (i : Fin mX) : (old C s).HX i.castSucc = pad (C.HX i) :=
  by simp [old]
@[simp] theorem old_HX_last : (old C s).HX (Fin.last mX) = Fin.snoc s 1 :=
  by simp [old]
@[simp] theorem old_HZ (j : Fin mZ) : (old C s).HZ j = liftZ s (C.HZ j) := rfl

private theorem map_mem_span {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 2))
    (f : Vec b →ₗ[ZMod 2] Vec (n + 1)) (S : Submodule (ZMod 2) (Vec (n + 1)))
    (h : ∀ i, f (M i) ∈ S) {x : Vec b}
    (hx : x ∈ Submodule.span (ZMod 2) (Set.range M)) : f x ∈ S := by
  exact (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i) :
    Submodule.span (ZMod 2) (Set.range M) ≤ S.comap f) hx

theorem pad_mem_xStab {x : Vec n} (hx : x ∈ C.xStab) : pad x ∈ (old C s).xStab := by
  apply map_mem_span C.HX pad (old C s).xStab _ hx
  intro i
  exact Submodule.subset_span ⟨i.castSucc, old_HX_castSucc C s i⟩

theorem liftZ_mem_zStab {z : Vec n} (hz : z ∈ C.zStab) : liftZ s z ∈ (old C s).zStab := by
  apply map_mem_span C.HZ (liftZ s) (old C s).zStab _ hz
  intro j
  exact Submodule.subset_span ⟨j, rfl⟩

theorem liftX_mem_xStab {x : Vec n} (hx : x ∈ C.xStab) (t : ZMod 2) :
    liftX s x t ∈ (old C s).xStab := by
  have he : Fin.snoc s 1 ∈ (old C s).xStab :=
    Submodule.subset_span ⟨Fin.last mX, old_HX_last C s⟩
  have h := (old C s).xStab.add_mem (pad_mem_xStab C s hx) ((old C s).xStab.smul_mem t he)
  convert h using 1
  ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftX, pad]

/-- The old X boundary space is exactly the preimage of the new one. -/
theorem mem_xStab_iff (y : Vec (n + 1)) :
    y ∈ (old C s).xStab ↔ decodeX s y ∈ C.xStab := by
  constructor
  · intro hy
    apply (show (old C s).xStab ≤ C.xStab.comap (decodeX s) from ?_) hy
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change decodeX s ((old C s).HX i) ∈ C.xStab
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [decodeX, old]
    · simpa [decodeX, pad] using (Submodule.subset_span ⟨j, rfl⟩ : C.HX j ∈ C.xStab)
  · intro h
    simpa using liftX_mem_xStab C s h (y (Fin.last n))

/-- The old Z boundary space is precisely the graph of s dot (-) on the new one. -/
theorem mem_zStab_iff (y : Vec (n + 1)) :
    y ∈ (old C s).zStab ↔ ∃ z ∈ C.zStab, liftZ s z = y := by
  change y ∈ Submodule.span _ _ ↔ y ∈ C.zStab.map (liftZ s)
  rw [CSSCode.zStab, Submodule.map_span]
  have he : Set.range (old C s).HZ = (liftZ s) '' Set.range C.HZ := by
    ext z
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨C.HZ i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [he]

@[simp] theorem liftZ_mem_iff (z : Vec n) :
    liftZ s z ∈ (old C s).zStab ↔ z ∈ C.zStab := by
  rw [mem_zStab_iff]
  constructor
  · rintro ⟨w, hw, he⟩
    have h := congrArg Fin.init he
    have hwz : w = z := by simpa [liftZ] using h
    exact hwz ▸ hw
  · intro h; exact ⟨z, h, rfl⟩

/-- Commutation with old Z checks is exactly the new X cycle condition after decoding. -/
theorem x_cycle_iff (y : Vec (n + 1)) :
    (old C s).HZ.mulVec y = 0 ↔ C.HZ.mulVec (decodeX s y) = 0 := by
  have hd (j : Fin mZ) : (old C s).HZ j ⬝ᵥ y = C.HZ j ⬝ᵥ decodeX s y := by
    change Fin.snoc (C.HZ j) (s ⬝ᵥ C.HZ j) ⬝ᵥ y =
      C.HZ j ⬝ᵥ (Fin.init y - y (Fin.last n) • s)
    rw [snoc_dot_any, dotProduct_sub, dotProduct_smul, dotProduct_comm s (C.HZ j)]
    simp [sub_eq_add_neg, CharTwo.neg_eq, mul_comm]
  simp only [funext_iff, Matrix.mulVec, Pi.zero_apply, hd]

/-- Every old Z cycle has a unique forced last coordinate. -/
theorem z_cycle_iff (y : Vec (n + 1)) :
    (old C s).HX.mulVec y = 0 ↔
      C.HX.mulVec (Fin.init y) = 0 ∧ y = liftZ s (Fin.init y) := by
  constructor
  · intro h
    have hlast := congrFun h (Fin.last mX)
    have he : y (Fin.last n) = s ⬝ᵥ Fin.init y := by
      have hz : s ⬝ᵥ Fin.init y + y (Fin.last n) = 0 := by
        simpa [Matrix.mulVec, old] using hlast
      simpa [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hz
    refine ⟨?_, ?_⟩
    · ext i
      simpa [Matrix.mulVec, old, pad] using congrFun h i.castSucc
    · calc
        y = Fin.snoc (Fin.init y) (y (Fin.last n)) := (Fin.snoc_init_self y).symm
        _ = liftZ s (Fin.init y) := by rw [he]; rfl
  · rintro ⟨h, he⟩
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have ht := congrFun he (Fin.last n)
      simp only [liftZ] at ht
      simp [Matrix.mulVec, old, liftZ, ht, CharTwo.add_self_eq_zero]
    · simpa [Matrix.mulVec, old, pad] using congrFun h j

/-- Nontriviality is preserved for every X representative in the two-element fiber. -/
theorem x_logical_iff (y : Vec (n + 1)) :
    (old C s).IsXLogical y ↔ C.IsXLogical (decodeX s y) := by
  simp only [CSSCode.IsXLogical, x_cycle_iff, mem_xStab_iff]

/-- Z logicals are in bijection by the explicit parity lift. -/
theorem z_logical_iff (y : Vec (n + 1)) :
    (old C s).IsZLogical y ↔ C.IsZLogical (Fin.init y) ∧ y = liftZ s (Fin.init y) := by
  rw [CSSCode.IsZLogical, z_cycle_iff]
  constructor
  · rintro ⟨⟨hc, he⟩, hn⟩
    refine ⟨⟨hc, ?_⟩, he⟩
    intro hb; exact hn (he ▸ liftZ_mem_zStab C s hb)
  · rintro ⟨⟨hc, hn⟩, he⟩
    refine ⟨⟨hc, he⟩, ?_⟩
    rw [he, liftZ_mem_iff]; exact hn

@[simp] theorem liftX_logical_iff (x : Vec n) (t : ZMod 2) :
    (old C s).IsXLogical (liftX s x t) ↔ C.IsXLogical x := by
  rw [x_logical_iff, decode_liftX]

@[simp] theorem liftZ_logical_iff (z : Vec n) :
    (old C s).IsZLogical (liftZ s z) ↔ C.IsZLogical z := by
  simp [z_logical_iff, liftZ]

/-- The X stabilizer acquires exactly one independent generator. -/
def xStabEquiv : (C.xStab × ZMod 2) ≃ₗ[ZMod 2] (old C s).xStab where
  toFun p := ⟨liftX s p.1 p.2, liftX_mem_xStab C s p.1.property p.2⟩
  invFun y := (⟨decodeX s y, (mem_xStab_iff C s y).mp y.property⟩, y.1 (Fin.last n))
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext; exact decode_liftX s p.1 p.2
    · simp [liftX]
  right_inv y := by apply Subtype.ext; exact liftX_decode s y
  map_add' p q := by
    apply Subtype.ext
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftX, add_smul]
    ring
  map_smul' a p := by
    apply Subtype.ext
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [liftX]
    ring

/-- The Z stabilizer is the same vector space, embedded as a parity graph. -/
def zStabEquiv : C.zStab ≃ₗ[ZMod 2] (old C s).zStab where
  toFun z := ⟨liftZ s z, liftZ_mem_zStab C s z.property⟩
  invFun y := ⟨Fin.init y.1, by
    obtain ⟨z, hz, he⟩ := (mem_zStab_iff C s y).mp y.property
    have hi : z = Fin.init y.1 := by simpa [liftZ] using congrArg Fin.init he
    exact hi ▸ hz⟩
  left_inv z := by apply Subtype.ext; simp [liftZ]
  right_inv y := by
    apply Subtype.ext
    obtain ⟨z, hz, he⟩ := (mem_zStab_iff C s y).mp y.property
    have hi : z = Fin.init y.1 := by simpa [liftZ] using congrArg Fin.init he
    change liftZ s (Fin.init y.1) = y.1
    rw [← hi, he]
  map_add' z w := by apply Subtype.ext; exact (liftZ s).map_add _ _
  map_smul' a z := by apply Subtype.ext; exact (liftZ s).map_smul _ _

theorem rankX : finrank (ZMod 2) (old C s).xStab = finrank (ZMod 2) C.xStab + 1 := by
  rw [← (xStabEquiv C s).finrank_eq, Module.finrank_prod, Module.finrank_self]

theorem rankZ : finrank (ZMod 2) (old C s).zStab = finrank (ZMod 2) C.zStab :=
  (zStabEquiv C s).finrank_eq.symm

/-- The encoded-qubit formula is unchanged, including its natural-number subtraction. -/
theorem encoded_dimension :
    (n + 1) - finrank (ZMod 2) (old C s).xStab - finrank (ZMod 2) (old C s).zStab =
      n - finrank (ZMod 2) C.xStab - finrank (ZMod 2) C.zStab := by
  rw [rankX, rankZ]
  omega

/-- Hamming cost of a single physical bit. -/
def bitWeight (t : ZMod 2) : ℕ := if t = 0 then 0 else 1

theorem bitWeight_le_one (t : ZMod 2) : bitWeight t ≤ 1 := by
  unfold bitWeight; split <;> omega

@[simp] theorem snoc_weight (x : Vec n) (t : ZMod 2) :
    hammingNorm (Fin.snoc x t : Vec (n + 1)) = hammingNorm x + bitWeight t := by
  simp only [hammingNorm, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [bitWeight]

@[simp] theorem pad_weight (x : Vec n) : hammingNorm (pad x) = hammingNorm x := by
  simp [pad, bitWeight]

/-- Exact original-coordinate weight of either X lift. -/
theorem liftX_weight (x : Vec n) (t : ZMod 2) :
    hammingNorm (liftX s x t) = hammingNorm (x + t • s) + bitWeight t := by
  exact snoc_weight _ _

/-- Exact original-coordinate weight of the forced Z lift. -/
theorem liftZ_weight (z : Vec n) :
    hammingNorm (liftZ s z) = hammingNorm z + bitWeight (s ⬝ᵥ z) := by
  exact snoc_weight _ _

theorem liftZ_weight_bounds (z : Vec n) :
    hammingNorm z ≤ hammingNorm (liftZ s z) ∧
      hammingNorm (liftZ s z) ≤ hammingNorm z + 1 := by
  rw [liftZ_weight]
  have := bitWeight_le_one (s ⬝ᵥ z)
  omega

/-- Explicit X logical lift with no growth in original Hamming weight. -/
theorem logical_X_lift {x : Vec n} (hx : C.IsXLogical x) :
    (old C s).IsXLogical (pad x) ∧ hammingNorm (pad x) = hammingNorm x := by
  refine ⟨?_, pad_weight x⟩
  simpa using (liftX_logical_iff C s x 0).mpr hx

/-- Explicit Z logical lift with at most one additional original physical qubit. -/
theorem logical_Z_lift {z : Vec n} (hz : C.IsZLogical z) :
    (old C s).IsZLogical (liftZ s z) ∧
      hammingNorm z ≤ hammingNorm (liftZ s z) ∧
      hammingNorm (liftZ s z) ≤ hammingNorm z + 1 :=
  ⟨(liftZ_logical_iff C s z).mpr hz, liftZ_weight_bounds s z⟩

/-- The concrete lifts preserve the X/Z logical pairing, for either X representative. -/
theorem lift_pairing (x z : Vec n) (t : ZMod 2) :
    liftX s x t ⬝ᵥ liftZ s z = x ⬝ᵥ z := by
  simp [liftX, liftZ, add_dotProduct, smul_dotProduct, add_assoc, CharTwo.add_self_eq_zero]

/-- Exact X minimum in terms of the two physical representatives of each new logical. -/
theorem distX_old_iff (D : ℕ) : (old C s).DistX D ↔
    (∃ x t, C.IsXLogical x ∧ hammingNorm (x + t • s) + bitWeight t = D) ∧
      ∀ x, C.IsXLogical x → ∀ t, D ≤ hammingNorm (x + t • s) + bitWeight t := by
  constructor
  · rintro ⟨⟨y, hy, hw⟩, hl⟩
    refine ⟨⟨decodeX s y, y (Fin.last n), (x_logical_iff C s y).mp hy, ?_⟩, ?_⟩
    · rw [← liftX_weight, liftX_decode]; exact hw
    · intro x hx t
      simpa only [liftX_weight] using hl _ ((liftX_logical_iff C s x t).mpr hx)
  · rintro ⟨⟨x, t, hx, hw⟩, hl⟩
    refine ⟨⟨liftX s x t, (liftX_logical_iff C s x t).mpr hx, ?_⟩, ?_⟩
    · rw [liftX_weight]; exact hw
    · intro y hy
      have h := hl _ ((x_logical_iff C s y).mp hy) (y (Fin.last n))
      rwa [← liftX_weight, liftX_decode] at h

/-- Exact Z minimum, including the parity bit's possible cost of one. -/
theorem distZ_old_iff (D : ℕ) : (old C s).DistZ D ↔
    (∃ z, C.IsZLogical z ∧ hammingNorm z + bitWeight (s ⬝ᵥ z) = D) ∧
      ∀ z, C.IsZLogical z → D ≤ hammingNorm z + bitWeight (s ⬝ᵥ z) := by
  constructor
  · rintro ⟨⟨y, hy, hw⟩, hl⟩
    obtain ⟨hz, he⟩ := (z_logical_iff C s y).mp hy
    refine ⟨⟨Fin.init y, hz, ?_⟩, ?_⟩
    · rw [← liftZ_weight, ← he]; exact hw
    · intro z hz
      simpa only [liftZ_weight] using hl _ ((liftZ_logical_iff C s z).mpr hz)
  · rintro ⟨⟨z, hz, hw⟩, hl⟩
    refine ⟨⟨liftZ s z, (liftZ_logical_iff C s z).mpr hz, ?_⟩, ?_⟩
    · rw [liftZ_weight]; exact hw
    · intro y hy
      obtain ⟨hz, he⟩ := (z_logical_iff C s y).mp hy
      rw [he, liftZ_weight]
      exact hl _ hz

/-- A lower bound on the old X distance also bounds the new X distance. -/
theorem new_X_lower {D : ℕ}
    (h : ∀ y, (old C s).IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, C.IsXLogical x → D ≤ hammingNorm x := by
  intro x hx
  simpa using h (liftX s x 0) ((liftX_logical_iff C s x 0).mpr hx)

/-- On Z, deletion can lose at most one unit of distance. -/
theorem new_Z_lower {D : ℕ}
    (h : ∀ y, (old C s).IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, C.IsZLogical z → D - 1 ≤ hammingNorm z := by
  intro z hz
  have hl := h _ ((liftZ_logical_iff C s z).mpr hz)
  have hu := (liftZ_weight_bounds s z).2
  omega

/-- A new Z lower bound already bounds every old Z logical. -/
theorem old_Z_lower {D : ℕ} (h : ∀ z, C.IsZLogical z → D ≤ hammingNorm z) :
    ∀ y, (old C s).IsZLogical y → D ≤ hammingNorm y := by
  intro y hy
  obtain ⟨hz, he⟩ := (z_logical_iff C s y).mp hy
  have hl := h _ hz
  have hw := (liftZ_weight_bounds s (Fin.init y)).1
  rw [← he] at hw
  omega

/-- A shortest new Z logical with zero pairing is a substantive preservation witness. -/
theorem distZ_preserved {D : ℕ} (h : C.DistZ D)
    (hw : ∃ z, C.IsZLogical z ∧ hammingNorm z = D ∧ s ⬝ᵥ z = 0) :
    (old C s).DistZ D := by
  obtain ⟨z, hz, he, hp⟩ := hw
  refine ⟨⟨liftZ s z, (liftZ_logical_iff C s z).mpr hz, ?_⟩, old_Z_lower C s h.2⟩
  simp [liftZ_weight, hp, bitWeight, he]

/-- Exact X preservation criterion: the other representative must not undercut D. -/
theorem distX_preserved_iff {D : ℕ} (h : C.DistX D) :
    (old C s).DistX D ↔ ∀ x, C.IsXLogical x → D ≤ hammingNorm (x + s) + 1 := by
  constructor
  · intro ho x hx
    have hl := ho.2 _ ((liftX_logical_iff C s x 1).mpr hx)
    simpa [liftX_weight, bitWeight] using hl
  · intro hb
    rw [distX_old_iff]
    obtain ⟨x, hx, hw⟩ := h.1
    refine ⟨⟨x, 0, hx, by simpa [bitWeight] using hw⟩, ?_⟩
    intro y hy t
    fin_cases t
    · change D ≤ hammingNorm (y + (0 : ZMod 2) • s) + bitWeight 0
      simpa [bitWeight] using h.2 y hy
    · change D ≤ hammingNorm (y + (1 : ZMod 2) • s) + bitWeight 1
      simpa [bitWeight] using hb y hy

/-- Exact Z preservation criterion: at least one shortest new logical has even pairing. -/
theorem distZ_preserved_iff {D : ℕ} (h : C.DistZ D) :
    (old C s).DistZ D ↔ ∃ z, C.IsZLogical z ∧ hammingNorm z = D ∧ s ⬝ᵥ z = 0 := by
  constructor
  · intro ho
    obtain ⟨y, hy, hw⟩ := ho.1
    obtain ⟨hz, he⟩ := (z_logical_iff C s y).mp hy
    rw [he, liftZ_weight] at hw
    have hl := h.2 _ hz
    have hn : hammingNorm (Fin.init y) = D := by omega
    refine ⟨Fin.init y, hz, hn, ?_⟩
    have hb : bitWeight (s ⬝ᵥ Fin.init y) = 0 := by omega
    by_contra hp
    simp [bitWeight, hp] at hb
  · exact distZ_preserved C s h

/-- Exact one-unit Z loss on deletion: all shortest new Z logicals have odd pairing. -/
theorem distZ_loss_iff {D : ℕ} (h : C.DistZ D) :
    (old C s).DistZ (D + 1) ↔
      ∀ z, C.IsZLogical z → hammingNorm z = D → s ⬝ᵥ z ≠ 0 := by
  constructor
  · intro ho z hz hw hp
    have hl := ho.2 _ ((liftZ_logical_iff C s z).mpr hz)
    simp [liftZ_weight, bitWeight, hp, hw] at hl
  · intro hp
    rw [distZ_old_iff]
    obtain ⟨z, hz, hw⟩ := h.1
    refine ⟨⟨z, hz, by simp [hw, bitWeight, hp z hz hw]⟩, ?_⟩
    intro w hw'
    have hl := h.2 w hw'
    by_cases he : hammingNorm w = D
    · simp [he, bitWeight, hp w hw' he]
    · omega

/-- The two asymmetric distance comparisons, when both minima are supplied. -/
theorem distance_comparison {a b c d : ℕ}
    (hox : (old C s).DistX a) (hoz : (old C s).DistZ b)
    (hnx : C.DistX c) (hnz : C.DistZ d) : a ≤ c ∧ d ≤ b ∧ b ≤ d + 1 := by
  obtain ⟨x, hx, hwx⟩ := hnx.1
  have hX := new_X_lower C s hox.2 x hx
  obtain ⟨y, hy, hwy⟩ := hoz.1
  have hZ := old_Z_lower C s hnz.2 y hy
  obtain ⟨z, hz, hwz⟩ := hnz.1
  have hu := hoz.2 _ ((liftZ_logical_iff C s z).mpr hz)
  have hb := (liftZ_weight_bounds s z).2
  omega

end QldpcVerification.QubitRemoval
