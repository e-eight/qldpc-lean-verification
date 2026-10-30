import QldpcVerification.Boundary566Stage0

/-! Literal endpoints and composition of all twelve certified elementary removals. -/
namespace QldpcVerification.Removal566
open Matrix Module Input Input.Sparse QubitRemoval QubitRemovalTransport QubitRemovalSequence
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The exact submitted endpoints, including their literal row order. -/
abbrev source := Stage0.code
abbrev target := Stage12.code

theorem source_HX : source.HX = matrix Stage0.hx := Stage0.hx_eq
theorem source_HZ : source.HZ = matrix Stage0.hz := Stage0.hz_eq
theorem target_HX : target.HX = matrix Stage12.hx := Stage12.hx_eq
theorem target_HZ : target.HZ = matrix Stage12.hz := Stage12.hz_eq

theorem ranks : finrank (ZMod 2) source.xStab = 280 ∧
    finrank (ZMod 2) source.zStab = 280 ∧
    finrank (ZMod 2) target.xStab = 274 ∧ finrank (ZMod 2) target.zStab = 274 :=
  ⟨Stage0.rankX, Stage0.rankZ, Stage12.rankX, Stage12.rankZ⟩

theorem encoded_dimensions :
    578 - finrank (ZMod 2) source.xStab - finrank (ZMod 2) source.zStab = 18 ∧
    566 - finrank (ZMod 2) target.xStab - finrank (ZMod 2) target.zStab = 18 := by
  constructor
  · exact Stage0.encoded_dimension
  · rw [Stage12.rankX, Stage12.rankZ]

/-- Conditional transport: the certificate supplies no source distance lower bound. -/
theorem lower_X {D : ℕ}
    (h : ∀ y, source.IsXLogical y → D ≤ hammingNorm y) :
    ∀ x, target.IsXLogical x → D ≤ hammingNorm x := by
  have h1 := Stage0.lowerX h
  have h2 := Stage1.lowerX h1
  have h3 := Stage2.lowerX h2
  have h4 := Stage3.lowerX h3
  have h5 := Stage4.lowerX h4
  have h6 := Stage5.lowerX h5
  have h7 := Stage6.lowerX h6
  have h8 := Stage7.lowerX h7
  have h9 := Stage8.lowerX h8
  have h10 := Stage9.lowerX h9
  have h11 := Stage10.lowerX h10
  have h12 := Stage11.lowerX h11
  exact h12

theorem lower_Z {D : ℕ}
    (h : ∀ y, source.IsZLogical y → D ≤ hammingNorm y) :
    ∀ z, target.IsZLogical z → D - 6 ≤ hammingNorm z := by
  have h1 := Stage0.lowerZ h
  have h2 := Stage1.lowerZ h1
  have h3 := Stage2.lowerZ h2
  have h4 := Stage3.lowerZ h3
  have h5 := Stage4.lowerZ h4
  have h6 := Stage5.lowerZ h5
  have h7 := Stage6.lowerZ h6
  have h8 := Stage7.lowerZ h7
  have h9 := Stage8.lowerZ h8
  have h10 := Stage9.lowerZ h9
  have h11 := Stage10.lowerZ h10
  have h12 := Stage11.lowerZ h11
  simpa only [Nat.sub_sub] using h12

/-- Hypothetical source lower bounds of twenty give only twenty/fourteen here. -/
theorem conditional_twenty
    (hx : ∀ x, source.IsXLogical x → 20 ≤ hammingNorm x)
    (hz : ∀ z, source.IsZLogical z → 20 ≤ hammingNorm z) :
    (∀ x, target.IsXLogical x → 20 ≤ hammingNorm x) ∧
    (∀ z, target.IsZLogical z → 14 ≤ hammingNorm z) :=
  ⟨lower_X hx, lower_Z hz⟩

end QldpcVerification.Removal566
