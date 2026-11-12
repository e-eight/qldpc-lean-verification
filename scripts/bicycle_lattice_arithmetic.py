"""Emit analytic integer-basis proofs for normalized cyclic bicycle lattices.

Basis reduction is a discovery procedure, not a Lean premise. The generated
module proves four integer identities, two strict bounds, and four vector
norm inequalities, then applies the symbolic BasisSeparation theorem.
"""

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class AnalyticBasis:
    p: tuple[int, int]
    q: tuple[int, int]
    p_period: int
    q_period: int
    witness: tuple[int, int]

    @property
    def vectors(self):
        return (
            self.p,
            self.q,
            tuple(x + y for x, y in zip(self.p, self.q, strict=True)),
            tuple(x - y for x, y in zip(self.p, self.q, strict=True)),
        )


def analytic_basis(m, a, distance):
    """Find and validate a two-vector analytic separation argument.

    Exact Gauss reduction uses swaps and integer shears, starting from
    (m, 0), (-a, 1). Every nonterminal shear strictly decreases the squared
    Euclidean norm of the second vector. No lattice window is searched.
    """
    if any(type(x) is not int for x in (m, a, distance)):
        raise ValueError("The period, step, and distance must be integers.")
    if m <= 0 or a < 0 or distance <= 0:
        raise ValueError("Require a positive period and distance and a nonnegative step.")
    p, q = (m, 0), (-a, 1)
    while True:
        p_squared = sum(x * x for x in p)
        q_squared = sum(x * x for x in q)
        if p_squared > q_squared:
            p, q = q, p
            p_squared, q_squared = q_squared, p_squared
        dot = sum(x * y for x, y in zip(p, q, strict=True))
        if 2 * abs(dot) <= p_squared:
            break
        quotient = (abs(dot) + p_squared // 2) // p_squared
        if dot < 0:
            quotient = -quotient
        reduced = tuple(y - quotient * x for x, y in zip(p, q, strict=True))
        if sum(x * x for x in reduced) >= q_squared:
            raise RuntimeError("The exact basis-reduction potential did not decrease.")
        q = reduced
    if p[0] * q[1] - q[0] * p[1] < 0:
        q = tuple(-x for x in q)
    if p[0] * q[1] - q[0] * p[1] != m:
        raise RuntimeError("Integer basis reduction changed the lattice determinant.")
    p_period, p_rem = divmod(p[0] + a * p[1], m)
    q_period, q_rem = divmod(q[0] + a * q[1], m)
    if p_rem or q_rem or p_period * q[1] - q_period * p[1] != 1:
        raise RuntimeError("The reduced vectors do not give integral lattice coordinates.")
    candidate = AnalyticBasis(p, q, p_period, q_period, (0, 0))
    for vector in candidate.vectors:
        if sum(map(abs, vector)) < distance:
            raise ValueError(f"Lattice relation {vector} is shorter than target {distance}.")
    if any(max(map(abs, vector)) * (distance - 1) >= 2 * m for vector in (p, q)):
        raise ValueError("The strict analytic inverse-coordinate bounds do not hold.")
    witness = next(
        (vector for vector in candidate.vectors if sum(map(abs, vector)) == distance), None
    )
    if witness is None:
        raise ValueError(f"No attaining relation has the requested length {distance}.")
    return AnalyticBasis(p, q, p_period, q_period, witness)


def emit_arithmetic(name, m, a, distance):
    """Return a complete Lean arithmetic module with no enumerative premise."""
    if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is None:
        raise ValueError("The Lean instance name must be an uppercase identifier.")
    basis = analytic_basis(m, a, distance)
    p1, p2 = basis.p
    q1, q2 = basis.q
    u, v = basis.witness
    period = (u + a * v) // m
    width = 2 * distance - 1
    radius = distance - 1
    return f"""import QldpcVerification.Lattice.BasisSeparation

/-! Analytic basis proof for `u + {a}v = 0 mod {m}`.
The two basis vectors are ({p1}, {p2}), ({q1}, {q2}); all checks below
are closed integer calculations. No finite lattice window is searched. -/

namespace QldpcVerification.Lattice.{name}Arithmetic

def basis : BasisSeparation.BasisData {m} {a} {distance} where
  p₁ := {p1}
  p₂ := {p2}
  q₁ := {q1}
  q₂ := {q2}
  pPeriod := {basis.p_period}
  qPeriod := {basis.q_period}
  p_relation := by norm_num
  q_relation := by norm_num
  quotient_det := by norm_num
  p_margin := by norm_num
  q_margin := by norm_num
  p_norm := by norm_num
  q_norm := by norm_num
  add_norm := by norm_num
  sub_norm := by norm_num

theorem bound (u v : ℤ) (hn : u ≠ 0 ∨ v ≠ 0)
    (hc : (1 : ZMod {m}) * (u : ZMod {m}) + {a} * (v : ZMod {m}) = 0) :
    {distance} ≤ u.natAbs + v.natAbs :=
  basis.bound (by norm_num) u v hn hc

theorem shortest_relation : ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧
    (1 : ZMod {m}) * (u : ZMod {m}) + {a} * (v : ZMod {m}) = 0 ∧
      u.natAbs + v.natAbs = {distance} := by
  refine ⟨{u}, {v}, ?_, ?_, ?_⟩
  · norm_num
  · have hd : ({m} : ℤ) ∣ ({u} : ℤ) + {a} * ({v} : ℤ) := ⟨{period}, by norm_num⟩
    have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (({u} : ℤ) + {a} * ({v} : ℤ)) {m}).mpr hd
    simpa only [one_mul, Int.cast_add, Int.cast_mul, Int.cast_neg,
      Int.cast_ofNat, Int.cast_one] using hc
  · norm_num

/-- Compatibility statement: the old window property follows from the analytic bound. -/
theorem finite_exclusion : ∀ i j : Fin {width},
    let u : ℤ := (i.val : ℤ) - {radius}
    let v : ℤ := (j.val : ℤ) - {radius}
    u.natAbs + v.natAbs ≤ {radius} → (u + {a} * v) % {m} = 0 → u = 0 ∧ v = 0 := by
  intro i j
  dsimp only
  intro hw hr
  by_contra hz
  have hn : (i.val : ℤ) - {radius} ≠ 0 ∨ (j.val : ℤ) - {radius} ≠ 0 := by tauto
  have h := basis.norm_ge (by norm_num) _ _ hn (Int.dvd_of_emod_eq_zero hr)
  omega

end QldpcVerification.Lattice.{name}Arithmetic
"""
