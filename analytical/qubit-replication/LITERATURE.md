# Attribution and scope

Date: 2026-11-11.

**PROPOSITION (bibliographic classification; independent review pending).**
Uniform qubit replication is concatenation with the length-r phase-flip
repetition code. No novelty is claimed for this code construction or for
the asymmetric distance multiplication. The contribution sought here is
a reusable, certificate-free Lean interface that identifies the actual
sparse check matrices, their stabilizer and cycle spaces, exact distances,
ranks, and sparsity bounds for every positive replication multiplicity.

The primary historical reference checked is Daniel Gottesman,
*Stabilizer Codes and Quantum Error Correction*, Caltech PhD thesis,
submitted 21 May 1997, arXiv:quant-ph/9705052, Section 3.5, printed pages
27–29, and Section 6.1, printed pages 60–62. Section 3.5 describes the
concatenated stabilizer as the inner stabilizers in every block together
with the outer stabilizers encoded through inner logical operators.
Section 6.1 describes encoding every physical qubit of an outer code in
an inner one-logical-qubit code.

- [ArXiv record](https://arxiv.org/abs/quant-ph/9705052)
- [Full thesis examined](https://thesis.caltech.edu/2900/02/THESIS.pdf)

For the present specialization, the inner X stabilizers are
`X_i X_anchor`, its logical X can be represented by `X_anchor`, and its
logical Z is the product of Z over every inner qubit. Substitution into
the construction in Section 3.5 gives exactly the displayed matrices in
the proof draft. The proof draft derives its exact distances directly
from parity and repetition maps; it does not invoke a general distance
multiplication assertion for arbitrary concatenated codes.

Searches used TinyFish Search and Fetch. Four query strings were examined:

1. `quantum CSS code concatenation repetition code asymmetric distance dX r dZ`
2. `quantum repetition code concatenation CSS "distance" "Gottesman"`
3. `"quantum codes" "repetition" "concatenation" asymmetric`
4. `Gottesman Stabilizer Codes Quantum Error Correction 1997 concatenated codes chapter 5`

There were 39 distinct result URLs. The full primary thesis was fetched
and its concatenation sections were checked. The Royal Society article
*Asymmetric quantum codes: constructions, bounds and performance* was
bot-blocked, so no claim relies on its inaccessible text. This search
establishes an explicit older construction covering the present one; it
does not assert an exhaustive priority history.
