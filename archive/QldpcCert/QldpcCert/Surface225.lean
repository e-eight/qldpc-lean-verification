import QldpcCert.SparseRank
import QldpcCert.Surface225Data
import QldpcCert.Surface225Support

/-!
# [[225,1,15]]: the 15×15 rotated surface code has distance exactly 15

The data in `QldpcCert/Surface225Data.lean` is generated from the board entry
`codes/225-1-15.json` by `scripts/gen_lean_instance.py`. Vectors are stored as
bitmasks: bit `q` set means qubit `q` is in the support.

Every finite fact is a `Bits` checker evaluated by Lean's kernel with
`decide +kernel`. There is no `native_decide`, so the proof rests on the kernel
alone.
-/

open Matrix Finset Module Bits

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Surface225

/-- `nq ≤ 2 ^ 8`, so eight folds compute every parity on these vectors. -/
theorem hK : nq ≤ 2 ^ 8 := by decide

theorem hn : 0 < nq := by decide

/-- Sparse supports are checked against every coordinate of the original rows. -/
theorem hxSupport_ok : sparseRowsCheck nq hx hxSupport = true := by decide +kernel

theorem hzSupport_ok : sparseRowsCheck nq hz hzSupport = true := by decide +kernel

/-- The code from the board entry. Commutation is checked in the kernel. -/
def code : CSSCode nq hx.length hz.length where
  HX := ofRows nq hx
  HZ := ofRows nq hz
  comm := comm_of_sparse nq hx hxSupport hz hxSupport_ok (by decide +kernel)

theorem rankX : tX.length ≤ finrank (ZMod 2) code.xStab :=
  rank_le_sparse nq hn hx hxSupport tX pX xPivotSupport hxSupport_ok
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rankZ : tZ.length ≤ finrank (ZMod 2) code.zStab :=
  rank_le_sparse nq hn hz hzSupport tZ pZ zPivotSupport hzSupport_ok
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The stabilizer ranks leave room for one logical qubit. -/
theorem dim : nq ≤ finrank (ZMod 2) code.xStab + finrank (ZMod 2) code.zStab + 1 := by
  have h1 := rankX
  have h2 := rankZ
  have : tX.length = 112 := by decide +kernel
  have : tZ.length = 112 := by decide +kernel
  have : nq = 225 := rfl
  omega

theorem dim_swap :
    nq ≤ finrank (ZMod 2) code.swap.xStab + finrank (ZMod 2) code.swap.zStab + 1 := by
  have h := dim
  change nq ≤ finrank (ZMod 2) code.zStab + finrank (ZMod 2) code.xStab + 1
  omega

/-! ## X side: Z-type lines -/

/-- Disjoint Z-type lines, each pairing to `1` with the X witness. -/
def zL (i : Fin zLines.length) : Vec nq := vec nq (zLines.get i)

theorem zLines_length : zLines.length = 15 := by decide +kernel

theorem zL_ker (i : Fin zLines.length) : code.HX.mulVec (zL i) = 0 := by
  have h : allOf (sparseKerCheck nq hx hxSupport) zLines = true := by decide +kernel
  exact mulVec_eq_zero_sparse nq hx hxSupport hxSupport_ok _ (allOf_spec _ _ h _ (List.get_mem _ i))

theorem zL_pair (i : Fin zLines.length) : vec nq wX ⬝ᵥ zL i = 1 := by
  have h : allOf (dotBit nq 8 wX) zLines = true := by decide +kernel
  exact dotProduct_eq_one nq 8 _ _ hK (allOf_spec _ _ h _ (List.get_mem _ i))

theorem zL_cover (q : Fin nq) : (univ.filter fun i => zL i q ≠ 0).card ≤ 1 :=
  cover_le_one nq zLines (by decide +kernel) q

theorem wX_ker : code.HZ.mulVec (vec nq wX) = 0 :=
  mulVec_eq_zero_sparse nq hz hzSupport hzSupport_ok wX (by decide +kernel)

theorem wX_weight : hammingNorm (vec nq wX) = 15 := by
  rw [hammingNorm_vec]
  decide +kernel

instance : Nonempty (Fin zLines.length) := ⟨⟨0, by rw [zLines_length]; decide⟩⟩

theorem distX : code.DistX 15 := by
  refine ⟨⟨vec nq wX, ⟨wX_ker, fun hmem => ?_⟩, wX_weight⟩, fun x hx => ?_⟩
  · let i0 : Fin zLines.length := ⟨0, by rw [zLines_length]; decide⟩
    have h := CSSCode.dotProduct_eq_zero_of_mem_span code.HX (zL_ker i0) hmem
    rw [zL_pair i0] at h
    exact one_ne_zero h
  · have h := code.distX_ge_of_packing (vec nq wX) wX_ker zL zL_ker zL_pair 1 zL_cover dim x hx
    simpa [zLines_length] using h

/-! ## Z side: X-type lines -/

/-- Disjoint X-type lines, each pairing to `1` with the Z witness. -/
def xL (i : Fin xLines.length) : Vec nq := vec nq (xLines.get i)

theorem xLines_length : xLines.length = 15 := by decide +kernel

theorem xL_ker (i : Fin xLines.length) : code.HZ.mulVec (xL i) = 0 := by
  have h : allOf (sparseKerCheck nq hz hzSupport) xLines = true := by decide +kernel
  exact mulVec_eq_zero_sparse nq hz hzSupport hzSupport_ok _ (allOf_spec _ _ h _ (List.get_mem _ i))

theorem xL_pair (i : Fin xLines.length) : vec nq wZ ⬝ᵥ xL i = 1 := by
  have h : allOf (dotBit nq 8 wZ) xLines = true := by decide +kernel
  exact dotProduct_eq_one nq 8 _ _ hK (allOf_spec _ _ h _ (List.get_mem _ i))

theorem xL_cover (q : Fin nq) : (univ.filter fun i => xL i q ≠ 0).card ≤ 1 :=
  cover_le_one nq xLines (by decide +kernel) q

theorem wZ_ker : code.HX.mulVec (vec nq wZ) = 0 :=
  mulVec_eq_zero_sparse nq hx hxSupport hxSupport_ok wZ (by decide +kernel)

theorem wZ_weight : hammingNorm (vec nq wZ) = 15 := by
  rw [hammingNorm_vec]
  decide +kernel

instance : Nonempty (Fin xLines.length) := ⟨⟨0, by rw [xLines_length]; decide⟩⟩

theorem distZ : code.DistZ 15 := by
  rw [CSSCode.distZ_iff_swap]
  refine ⟨⟨vec nq wZ, ⟨wZ_ker, fun hmem => ?_⟩, wZ_weight⟩, fun x hx => ?_⟩
  · let i0 : Fin xLines.length := ⟨0, by rw [xLines_length]; decide⟩
    have h := CSSCode.dotProduct_eq_zero_of_mem_span code.HZ (xL_ker i0) hmem
    rw [xL_pair i0] at h
    exact one_ne_zero h
  · have h := code.swap.distX_ge_of_packing (vec nq wZ) wZ_ker xL xL_ker xL_pair 1 xL_cover
      dim_swap x hx
    simpa [xLines_length] using h

/-- **The [[225,1,15]] rotated surface code on the board has distance exactly 15.** -/
theorem distance : code.DistX 15 ∧ code.DistZ 15 := ⟨distX, distZ⟩

end Surface225
