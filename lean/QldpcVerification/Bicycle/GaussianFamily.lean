import QldpcVerification.Bicycle.ShortestVector
import QldpcVerification.Lattice.Gaussian

/-! Exact parameters for an infinite family with coprime perpendicular period directions. -/

namespace QldpcVerification.Bicycle.GaussianFamily

open Module Connected

variable (a b h : ℕ) [NeZero (h * (a ^ 2 + b ^ 2))]

def matching := canonicalMatch (h * (a ^ 2 + b ^ 2)) a b

abbrev code := (matching a b h).code

theorem parameters (ha : 0 < a) (hh : 0 < h) (hab : Nat.Coprime a b) :
    (2 * (h * (a ^ 2 + b ^ 2)) - finrank (ZMod 2) (code a b h).xStab -
      finrank (ZMod 2) (code a b h).zStab = 2) ∧
      (code a b h).DistX (a + b) ∧ (code a b h).DistZ (a + b) := by
  have hc : Nat.gcd (Nat.gcd a b) (h * (a ^ 2 + b ^ 2)) = 1 := by
    simp [hab.gcd_eq_one]
  have hp := (matching a b h).parameters_of_shortest (a + b) hc
    (Lattice.Gaussian.norm_ge_of_cast a b h ha hh hab)
    ⟨(b : ℤ), -(a : ℤ), by simpa only [Int.cast_neg] using
      Lattice.Gaussian.minimizing_pair a b h ha⟩
  simpa only [two_mul] using hp

theorem ranks (hab : Nat.Coprime a b) :
    finrank (ZMod 2) (code a b h).xStab = h * (a ^ 2 + b ^ 2) - 1 ∧
    finrank (ZMod 2) (code a b h).zStab = h * (a ^ 2 + b ^ 2) - 1 := by
  have hc : Nat.gcd (Nat.gcd a b) (h * (a ^ 2 + b ^ 2)) = 1 := by
    simp [hab.gcd_eq_one]
  exact ⟨(matching a b h).rankX hc, (matching a b h).rankZ hc⟩

end QldpcVerification.Bicycle.GaussianFamily
