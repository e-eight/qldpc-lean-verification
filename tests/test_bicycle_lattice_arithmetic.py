import pytest
from bicycle_lattice_arithmetic import analytic_basis, emit_arithmetic


def test_minimum_can_be_basis_difference():
    basis = analytic_basis(131, 20, 15)
    assert sum(map(abs, basis.p)) > 15
    assert sum(map(abs, basis.q)) > 15
    assert basis.witness == tuple(x - y for x, y in zip(basis.p, basis.q, strict=True))
    assert (basis.witness[0] + 20 * basis.witness[1]) % 131 == 0
    assert sum(map(abs, basis.witness)) == 15


def test_reduction_uses_exact_half_boundary():
    basis = analytic_basis(8, 3, 4)
    dot = sum(x * y for x, y in zip(basis.p, basis.q, strict=True))
    assert 2 * abs(dot) == sum(x * x for x in basis.p)
    assert basis.p_period * basis.q[1] - basis.q_period * basis.p[1] == 1


def test_large_step_and_zero_step():
    for m, a, distance in [(29, 8 + 29 * 10**20, 7), (5, 0, 1)]:
        basis = analytic_basis(m, a, distance)
        assert basis.p[0] + a * basis.p[1] == m * basis.p_period
        assert basis.q[0] + a * basis.q[1] == m * basis.q_period
        assert basis.p[0] * basis.q[1] - basis.q[0] * basis.p[1] == m
        assert sum(map(abs, basis.witness)) == distance


@pytest.mark.parametrize("distance", [8, 20])
def test_rejects_false_lower_bound(distance):
    with pytest.raises(ValueError, match="shorter than target"):
        analytic_basis(29, 8, distance)


def test_rejects_unattained_claimed_distance():
    with pytest.raises(ValueError, match="No attaining relation"):
        analytic_basis(29, 8, 6)


@pytest.mark.parametrize("args", [(0, 1, 1), (7, -1, 2), (7, 1, 0), (True, 1, 1)])
def test_rejects_invalid_domain(args):
    with pytest.raises(ValueError):
        analytic_basis(*args)


def test_emits_symbolic_bound_and_attaining_pair():
    source = emit_arithmetic("Example", 131, 20, 15)
    assert "BasisSeparation.BasisData 131 20 15" in source
    assert "basis.bound" in source
    assert "theorem shortest_relation" in source
    assert "basis.norm_ge" in source
    assert "decide" not in source
