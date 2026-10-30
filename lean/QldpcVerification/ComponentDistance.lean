import QldpcVerification.Components
import QldpcVerification.CoverageTransport

/-! Exact distance of identical independent components equals their common distance. -/

namespace QldpcVerification.Components

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Nonempty I]

def Distance (S B : Submodule (ZMod 2) (E → ZMod 2)) (D : ℕ) : Prop :=
  (∃ x, x ∈ S ∧ x ∉ B ∧ hammingNorm x = D) ∧
    ∀ x, x ∈ S → x ∉ B → D ≤ hammingNorm x

theorem distance_product_iff (S B : Submodule (ZMod 2) (E → ZMod 2)) (D : ℕ) :
    Distance (product (I := I) S) (product B) D ↔ Distance S B D := by
  classical
  let i : I := Classical.arbitrary I
  have local_lower (h : Distance (product (I := I) S) (product B) D)
      (x : E → ZMod 2) (hx : x ∈ S) (hb : x ∉ B) : D ≤ hammingNorm x := by
    obtain ⟨hs, hn⟩ := extend_nonboundary i x hx hb
    simpa only [extend_weight] using h.2 _ hs hn
  constructor
  · intro h
    obtain ⟨x, hx, hb, hw⟩ := h.1
    have hn : ∃ j, slice j x ∉ B := by simpa [product] using hb
    obtain ⟨j, hj⟩ := hn
    have hl := local_lower h (slice j x) (hx j) hj
    have hu := slice_weight_le j x
    refine ⟨⟨slice j x, hx j, hj, ?_⟩, local_lower h⟩
    omega
  · rintro ⟨⟨x, hx, hb, hw⟩, hl⟩
    obtain ⟨hs, hn⟩ := extend_nonboundary i x hx hb
    exact ⟨⟨extend i x, hs, hn, (extend_weight i x).trans hw⟩, lower D hl⟩

theorem distance_reindex_iff {Q : Type} [Fintype Q] [DecidableEq Q]
    (e : E ≃ Q) {S B : Submodule (ZMod 2) (E → ZMod 2)}
    {T U : Submodule (ZMod 2) (Q → ZMod 2)}
    (hS : ∀ x, pull e x ∈ S ↔ x ∈ T) (hB : ∀ x, pull e x ∈ B ↔ x ∈ U) (D : ℕ) :
    Distance T U D ↔ Distance S B D := by
  constructor
  · rintro ⟨⟨x, hx, hb, hw⟩, hl⟩
    refine ⟨⟨pull e x, (hS x).mpr hx, fun h => hb ((hB x).mp h), (pull_weight e x).trans hw⟩, ?_⟩
    intro y hy hn
    have hs : (pull e).symm y ∈ T := (hS _).mp (by simpa using hy)
    have hb' : (pull e).symm y ∉ U := by
      intro h
      apply hn
      simpa using (hB _).mpr h
    have h := hl _ hs hb'
    simpa only [← pull_weight e, LinearEquiv.apply_symm_apply] using h
  · rintro ⟨⟨x, hx, hb, hw⟩, hl⟩
    have hs : (pull e).symm x ∈ T := (hS _).mp (by simpa using hx)
    have hn : (pull e).symm x ∉ U := by
      intro h
      apply hb
      simpa using (hB _).mpr h
    refine ⟨⟨(pull e).symm x, hs, hn, ?_⟩, ?_⟩
    · simpa only [← pull_weight e, LinearEquiv.apply_symm_apply] using hw
    · intro y hy hb'
      have h := hl (pull e y) ((hS y).mpr hy) (fun h => hb' ((hB y).mp h))
      simpa only [pull_weight] using h

end QldpcVerification.Components
