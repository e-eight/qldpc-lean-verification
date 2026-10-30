# Prior work for the paired-removal mathematics

Literature assessment dated 2026-10-30, following the [566 investigation](../lifting-566-investigation/).
TinyFish searches covered asymmetric puncturing, classical code minors, and exact logical-weight calculations.
Seventeen searches and five fetch batches exposed 115 distinct source URLs.
Fourteen primary documents supplied full text for the relevant definitions and proofs.
One further arXiv page supplied metadata.
Search-result URLs count toward coverage, not toward the number of papers read.
The assessment does not establish historical priority or first formalization.

## Assessment by claim

| Claim from the investigation | Prior-work assessment | Guidance |
| --- | --- | --- |
| Elementary CSS removal preserves k; one side cannot decrease and the other loses at most one | Known asymmetric puncturing result | Cite Grassl, Theorem 4, and its attribution to La Guardia (2013), Theorem 4.2. |
| The one-qubit `old(C,s)` extension itself | CSS specialization of an existing embedded-code construction, after X/Z duality | Sayginel et al., Appendix D. This match does not provide a weight-isometry theorem. |
| Two deletions can cost at most one in overall distance | Known for a suitable alternating CSS construction | Grassl, Theorem 5. Our paired zero-fan cleanup is a specific instance with a stronger side-specific description. |
| Pivot choice does not change the shortened/punctured row spaces | Direct consequence of classical code definitions | A pivot chooses a basis for a coordinate kernel. It does not define that kernel. |
| Disjoint typed deletions commute at the level of final row spaces | Standard linear-code minor identity and an elementary CSS corollary | Keep the surjective restriction hypotheses that guarantee legal pivots and preserve k. |
| Correct a representative with a stabilizer if twice the support overlap is at least its weight | Elementary binary Hamming-weight identity | This is a useful sufficient condition, not evidence of a new theorem. |
| Exact parity criteria and paired composite minimum formulas | No identical statement located in the reviewed sources | These follow transparently from the proved representative decompositions and standard quotient-distance definitions. Treat them as explicit normal-form lemmas. |
| All 64 typed pair choices reproduce the 566 row spaces; the fan map has rank six on Z stabilizers | Specific checked properties of these inputs | Useful certificate data. They do not establish a new general construction theorem. |

## Closest mathematical sources

[Markus Grassl, New Quantum Codes from CSS Codes](https://arxiv.org/html/2208.05353v2)
defines shortening and puncturing in Section 2.1 and gives the asymmetric propagation rule in Theorem 4.
Theorem 5 alternates the two types of removal.
The paper attributes the earlier asymmetric result to La Guardia's 2013 paper, *Asymmetric quantum codes: new codes from old*, Theorem 4.2.
The stated parameters give lower-bound guarantees. They do not assert equality of the exact distances after arbitrary deletions.
Grassl uses a side-distance hypothesis for arbitrary coordinate choice.
Our normal form instead supplies a distinguished active stabilizer pivot.
The local rank argument remains valid when a side distance is one.

[Sayginel et al., Fault-Tolerant Logical Clifford Gates from Code Automorphisms](https://arxiv.org/html/2409.18175v3)
gives a general embedded-code construction in Section VII and Appendix D.
Let A and B denote the retained X and Z checks.
With auxiliary qubits initialized to zero, its binary matrix M adds the checks
`X=(A,A M^T)` and `Z=(B,0),(M,I)` in the CSS case.
Our inference is that applying this construction to the dual CSS code, then exchanging X and Z, recovers `old(C,s)` for `M=s`.
The elementary extension is therefore a specialization of an established construction.
The CNOT embedding can change physical weight. Our explicit weight lemmas still need their own proof.

[Gundersen et al., Puncturing Quantum Stabilizer Codes](https://arxiv.org/html/2410.17754v3)
develops puncturing through a local symplectic constraint and row operations in Section III.
Propositions 3–4 and Section V use minimum-weight logical supports to improve generic loss bounds.
This supports the need to consider all relevant logical representatives, rather than a chosen logical basis.
The broader operation and its hypotheses must match an application before transferring a conclusion.

[Schrijver, Combinatorial Optimization, Chapter 39](https://page.math.tu-berlin.de/~felsner/Lehre/SemMatS/Literatur/Schrijver-39:Matroids.pdf)
states deletion/contraction commutation in Section 39.3, page 654, equation (39.11).
[Ruud Pellikaan's Arrangements, matroids and codes lectures](https://ruudp.win.tue.nl/lectures/11-07-20-slides-Leuven-3.pdf)
connect puncturing and shortening to these operations on slides 19–25.
Our row-space identities retain the represented subspaces, not only their abstract matroids.
They follow directly by imposing zero coordinates and projecting the remaining coordinates.
The CSS legality criterion also needs orthogonality and the stated full restriction ranks.

[Cao, Gullans, Lackey, and Wang, Quantum Lego Expansion Pack](https://arxiv.org/html/2308.05152v2)
defines stabilizer and normalizer coset weight enumerators in Definition III.2 and Proposition III.2.
[Grassl, Shor, and Zeng, Generalized Concatenation for Quantum Codes](https://arxiv.org/html/0905.0428v1)
also describes distances using normalizer differences and stabilizer exclusions in Section II.
These provide a general setting for minimizing weights over stabilizer-equivalent representatives.
Neither source, as reviewed, states our particular six-pair formulas verbatim.

## What the composite formulas add

For r removed pairs with retained fans f_i, the checked decomposition suggests

```text
dX_source = min_{x final X logical, t in F2^r}
              wt(x + sum_i t_i f_i) + 2 wt(t)
dZ_source = min_{z final Z logical} wt(z) + wt(R(z)),
R(z)_i = f_i dot z.
```

Here x and z range over actual nontrivial logical representatives, not one vector per logical class.
The X pair bits agree and cost two per occupied pair.
Each Z pair has prescribed parity and minimum cost zero or one.
These facts explain the formula without a new distance-search algorithm.
An explicit proof and a checked application remain useful even when the ingredients are standard.

In the 566 investigation, R maps the Z stabilizer space onto all six parity bits.
Thus every logical class contains a representative with R(z)=0.
This is an elementary consequence of surjectivity, not a distance-preservation theorem.
The correcting stabilizer can increase the retained weight.
The [kernel-checked four-to-three-qubit example](../../lean/QldpcVerification/QubitRemovalExamples.lean) already demonstrates this obstruction.
Its retained Z checks are `110,001`, and its fan is `111`.
The stabilizer parity map is onto. Its nontrivial class has even-parity representatives of weight two, but its minimum weight is one.
The old Z distance is two, so surjectivity does not prevent a distance drop.
The connection to surjectivity is a direct derivation from the example's matrices.
A theorem that supplies a weight-controlled correction for the relevant low-weight representatives remains a useful research target.
No novelty conclusion for such a future theorem follows from this search.

## Additional pair symmetry

The reviewer also derived a physical symmetry from the literal source rows.
Swapping either member of a deleted pair fixes every X row.
Each Z row changes by zero or by the existing Z pair stabilizer.
The six independent swaps therefore give a 64-element coordinate-automorphism subgroup of the source code.
Its action on logical quotients is trivial: X cycles have equal pair bits, and Z cycles change by pair stabilizers.
This explains the 64 typed choices through a physical symmetry, rather than only an endpoint row-space coincidence.
It remains an unformalized, elementary consequence of the pair structure.
Sayginel et al. provide the broader automorphism/embedding framework, not a verbatim theorem about these six pairs.
No novelty claim follows from this observation.

## Corrected hypotheses and related constructions

[Zeng and Pryadko's product-code paper](https://arxiv.org/abs/2007.12152)
explicitly records an erratum for its original Z-puncturing Lemma 1.
The corrected statement appears as Lemma 14 in
[Lin and Pryadko, Quantum two-block group algebra codes, Appendix A.5](https://arxiv.org/html/2306.16400v1).
It requires a logical X generator basis whose rows each lie within one of the two partition blocks.
The uncorrected unconditional lemma must not guide a proof.
Our approach instead proves the logical maps and nontriviality directly.

[Pabla, Wang, and Hong, Spatial overhead reduction for 2D hypergraph product codes](https://arxiv.org/html/2605.11318v1)
gives exact distance preservation in Theorem 3.7.
Its proof uses HGP logical-sector weight bounds and a specified reduction procedure.
The treatment retains the bit-type logical sector, with an explicit rank restriction or a subsystem interpretation for the other sector.
This is useful guidance for stronger structural lower bounds, not a theorem about arbitrary grafting or the 566 matrices.

Other full texts reviewed were the 2026 entanglement-assisted puncturing preprint
[Pedersen et al.](https://arxiv.org/html/2609.36273v1),
the distance-three pendant construction in
[Gupta et al., Section IV.1](https://arxiv.org/html/2501.12072v4),
and the [original product-code text](https://arxiv.org/html/2007.12152v3).
They supply adjacent constructions, not an identified identical paired-removal theorem.
The automorphism search also checked relevant portions of
[Koh et al., Achieving the limits of automorphism gates](https://arxiv.org/html/2609.19250v1)
and [Hao, Investigations on Automorphism Groups of Quantum Stabilizer Codes](https://math.berkeley.edu/~hhao/papers/Investigations%20on%20Automorphism%20Groups%20of%20Quantum%20Stabilizer%20Codes.pdf).
Neither supplied an identified identical paired-distance formula.
The APS erratum PDF was blocked, and the Fujita concatenation PDF was unreachable.
The assessment does not rely on unseen statements from either document.
