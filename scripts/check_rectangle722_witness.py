"""Check two supplied rectangle witnesses; never search for supports or logicals.

Python 3.13: uv run --locked --python 3.13 python scripts/check_rectangle722_witness.py
The Lean data block and self-contained appendix are checked byte for byte.
"""

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
X = (
    65,
    103,
    104,
    105,
    142,
    162,
    199,
    219,
    220,
    332,
    390,
    407,
    426,
    504,
    541,
    560,
    561,
    579,
    598,
    617,
    619,
    636,
    655,
)
Z = (46, 47, 61, 63, 65, 66, 80, 97, 131, 150, 167, 409, 424, 425, 446, 448, 456, 486, 487, 526)
F = ((1, 0), (2, 0), (0, 2))
G = ((0, 0), (2, 1), (2, 2))
RESIDUAL = {"X": ((1, 12), (19, 10), (19, 11)), "Z": ((3, -2), (3, -1), (4, 17), (6, 17))}
SHA256 = "4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15"
REVISION = "8c87413d16b78cdd934b7b7a8592cddc81ae6eed"
BEGIN = "-- BEGIN FIXED WITNESS DATA\n"
END = "-- END FIXED WITNESS DATA\n"


def products(sector, q):
    species, local = divmod(q, 361)
    i, j = divmod(local, 19)
    if sector == "X":
        shifts = F if species else G
        sign = 1
    else:
        shifts = G if species else F
        sign = -1
    return [(i + sign * a, j + sign * b) for a, b in shifts]


def cancellations(sector, support):
    counts = Counter(p for q in support for p in products(sector, q))
    assert tuple(sorted(p for p, count in counts.items() if count % 2)) == RESIDUAL[sector]
    residual = Counter(RESIDUAL[sector])
    pairs = []
    for p, count in sorted(counts.items()):
        assert (count - residual[p]) % 2 == 0
        pairs.extend([p] * ((count - residual[p]) // 2))
    assert counts == residual + Counter(pairs) + Counter(pairs)
    return pairs


def lean_data():
    lines = [BEGIN.rstrip()]
    for sector, support in (("X", X), ("Z", Z)):
        lower = sector.lower()
        lines += [f"def {lower}Support : List (Fin 722) :=\n  [{', '.join(map(str, support))}]"]
        for name, points in (
            ("Residual", RESIDUAL[sector]),
            ("Cancellation", cancellations(sector, support)),
        ):
            values = ", ".join(f"({i}, {j})" for i, j in points)
            lines += [f"def {lower}{name} : Multiset Lattice :=\n  {{{values}}}"]
    return "\n\n".join(lines) + "\n" + END


def appendix():
    text = f"""#set page(paper: "a4", margin: 18mm)
#set text(size: 10pt)
#set par(justify: false)
= A supplied weight-20 logical witness

*Upper-witness proposition (explicit rectangular model).* For the two check
matrices defined below, the displayed 23-qubit X vector and 20-qubit Z vector
are opposite-check cycles with binary pairing one. In particular, the Z vector
is a nontrivial logical of weight 20, and its pure-Z Pauli operator is a
nontrivial logical Pauli of weight 20. Thus the Z-sector and Pauli minimum
weights are at most 20. The X partner has weight 23. This proposition concerns
the explicitly defined model; applying it to the literal JSON requires the
separate ordered-input identification in INPUT.

This is a witness appendix, pending bounded Lean replay and three independent
reviews. It is not the final PROOF document. It supplies an upper bound of 20,
not an assertion that the distance equals 20. No search is used here.

The input is `qldpc-challenge/codes/722-8-20.json`, revision
`{REVISION}`. Its exact byte SHA-256 is
#linebreak()
#text(size: 8pt)[`{SHA256}`].
The separate INPUT appendix identifies its ordered matrices with the rectangle.
The supports here are the explicit pair recorded in `analytical/notes/geometry.md`.

= Model and check rows

All qubit labels start at zero. A(i,j) = 19i+j and B(i,j) = 361+19i+j,
where 0 ≤ i,j ≤ 18. The vector of a support has coefficient one at each
listed qubit and zero elsewhere. Work over the two-element field, so two
copies of any monomial cancel. Exponents in this appendix are ordinary
integers; there is no periodic wrap.

Let Q be the square of integer exponent pairs with 0 ≤ i,j ≤ 18. A physical
vector is a pair (u,v) of polynomials supported in Q, for species A and B.
Let P delete all terms outside Q in each component of a Laurent-polynomial
pair. Put f = x + x² + y² and g = 1 + x²y + x²y², and let bar replace
x and y by their inverses. Thus bar(f) = x⁻¹ + x⁻² + y⁻² and
bar(g) = 1 + x⁻²y⁻¹ + x⁻²y⁻². Define the binary check rows by

$ H_X[(a,b),:] = P(x^a y^b (f,g)), quad -2 <= a <= 18, quad 0 <= b <= 16; $
$ H_Z[(c,d),:] = P(x^c y^d (overline(g),overline(f))),
  quad 2 <= c <= 18, quad 0 <= d <= 20. $

These are actual integer anchor coordinates. They correspond to the input
indices (a+2,b) and (c−2,d), respectively. Both matrices have 357 rows and
722 columns. The dot product sums the products of corresponding A and B
coefficients over Q. No rank assertion is needed for this witness argument.

= Coefficients are check dot products

Write [i,j]h for the coefficient of x^i y^j in a Laurent polynomial h,
with coefficient zero at absent exponents. Multiplication is the finite
convolution [r,s](h u) = sum over (i,j) of ([r−i,s−j]h)([i,j]u).
Because u and v vanish outside Q, projecting a check row with P does not
change its dot product with (u,v). The Z row at (c,d) has A coefficient
[i−c,j−d]bar(g) = [c−i,d−j]g, and the analogous B coefficient uses f.
Consequently convolution gives

$ H_Z[(c,d),:] dot (u,v) = [c,d](g u + f v). $

For the X row at (a,b), the A coefficient is [i−a,j−b]f =
[a−i,b−j]bar(f), and the B coefficient similarly uses bar(g). Hence

$ H_X[(a,b),:] dot (u,v) = [a,b](overline(f) u + overline(g) v). $

These identities derive the full X syndrome g u + f v and full Z syndrome
bar(f) u + bar(g) v directly from the defined rows. Only coefficients at
retained check anchors are tested; the full polynomials may be nonzero outside
those anchors. No matrix computation or Lean result is a premise of this derivation.

= Commutation and retention of every overlap

Before projection, the X row at (a,b) has every y exponent in [b,b+2],
which lies in [0,18]. Thus all its columns lie on the physical board even
when some x exponents do not. Before projection, the Z row at (c,d) has
every x exponent in [c−2,c], which lies in [0,18]. Thus all its rows lie
on the physical board even when some y exponents do not. Any common
monomial of these two rows, in either species, therefore has both coordinates
in [0,18]. Projection discards no term that contributes to their dot product.

For finite Laurent polynomials h and k, their full-plane coefficient dot
product is the constant coefficient of h bar(k): each constant term pairs
equal exponent coordinates. Apply this componentwise to the two unprojected
check rows. The result is the constant coefficient of

$ x^(a-c) y^(b-d) (f g + g f). $

Polynomial multiplication commutes, and the field has characteristic two,
so fg + gf = 0. The full-plane row dot product is zero; retention of every
overlap proves the same for the projected physical rows. Hence
$H_X H_Z^T = 0$, so the rows define a commuting CSS stabilizer model.

= The two supplied supports

X support (23 distinct qubits):

{", ".join(map(str, X))}.

Z support (20 distinct qubits):

{", ".join(map(str, Z))}.

= Complete multiplication and cancellation

Each pair (i,j) below denotes x^i y^j. Each input row contributes exactly
the three exponent pairs in its product column. Nothing is truncated before
multiplication. The cancellation tables list a multiset C: every listed
entry is removed twice. Consequently the full product multiset is exactly
R + C + C, where R is the stated residual multiset. These are fixed integer
identities that can be checked by sorting the product columns and tallying.
"""
    for sector, support in (("X", X), ("Z", Z)):
        text += f"\n#pagebreak()\n== {sector} multiplication\n\n"
        text += "#table(columns: (35pt, 75pt, 1fr), inset: 3pt,\n"
        text += "  table.header([Qubit], [Input monomial], [Three product exponents]),\n"
        for q in support:
            species, local = divmod(q, 361)
            i, j = divmod(local, 19)
            terms = ", ".join(f"({a}, {b})" for a, b in products(sector, q))
            text += f"  [{q}], [{'B' if species else 'A'}({i}, {j})], [{terms}],\n"
        text += ")\n\nCancellation multiset C (each entry cancels twice):\n\n"
        text += ", ".join(f"({i}, {j})" for i, j in cancellations(sector, support)) + ".\n"
        text += "\nResidual multiset R: "
        text += ", ".join(f"({i}, {j})" for i, j in RESIDUAL[sector]) + ".\n"
    text += """
= Cycle, nontriviality, and upper bound

The X residual is x y¹² + x¹⁹ y¹⁰ + x¹⁹ y¹¹. Its first coordinates,
1 and 19, are outside the retained Z-check range 2 through 18.
The Z residual is x³ y⁻² + x³ y⁻¹ + x⁴ y¹⁷ + x⁶ y¹⁷.
Its second coordinates, −2, −1, and 17, are outside the retained X-check
range 0 through 16. Both actual opposite-check syndromes therefore vanish.

The displayed supports intersect in exactly {65}, so their binary dot
product is one. Every Z stabilizer is a sum of Z-check rows and pairs to
zero with the X cycle. Thus the displayed Z vector cannot be a Z stabilizer.
The same argument with X and Z interchanged makes the X vector nontrivial.
Counting the distinct Z labels gives weight 20; the X partner has weight 23.

The pure-Z Pauli operator placing Z on the 20 listed qubits and identity
elsewhere commutes with every stabilizer and is nontrivial modulo stabilizers.
Its Pauli weight is exactly 20. Hence the Z-sector minimum and the minimum
nontrivial Pauli weight are at most 20. The X partner only supplies an
X-sector upper bound of 23. No lower bound of 20 follows from these witnesses.

= Separate application to the submitted input

The proposition above uses only the explicit model definition and the supplied
supports. The ordered row identities in INPUT identify the literal submitted
matrices with this model in the same physical numbering, so the same vectors,
pairing, and weights give its upper witness. This is a separate input transport
step, not an assumption in the model proof. The persistent check script verifies the
closed polynomial products, weights, intersection, and sparse check parities;
these calculations are separate from the Lean kernel proof. No errors,
logical classes, or alternative supports are enumerated.
"""
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-appendix", action="store_true")
    parser.add_argument("--emit-data", action="store_true")
    args = parser.parse_args()
    if args.emit_data:
        print(lean_data(), end="")
        return
    raw = (
        Path(os.environ.get("QLDPC_REPO", ROOT.parent / "qldpc-challenge")) / "codes/722-8-20.json"
    ).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == SHA256
    checks = json.loads(raw)["checks"]
    assert len(X) == len(set(X)) == 23
    assert len(Z) == len(set(Z)) == 20
    assert set(X) & set(Z) == {65}
    for sector, support in (("X", X), ("Z", Z)):
        cancellations(sector, support)
        opposite = "Z" if sector == "X" else "X"
        assert all(len(set(row) & set(support)) % 2 == 0 for row in checks[opposite])
    path = ROOT / "analytical/rectangle722-submitted/WITNESS.typ"
    if args.write_appendix:
        path.write_text(appendix())
    else:
        assert path.read_bytes() == appendix().encode(), "appendix regeneration mismatch"
    lean = (ROOT / "lean/QldpcVerification/Rectangle722Witness.lean").read_text()
    block = BEGIN + lean.split(BEGIN, 1)[1].split(END, 1)[0] + END
    assert block == lean_data(), "fixed witness data mismatch"
    print("PASS: both polynomial identities; 714 sparse parities; intersection {65}; weights 23/20")
    print("PASS: fixed Lean data and appendix byte checks; Lean replay remains separate")


if __name__ == "__main__":
    main()
