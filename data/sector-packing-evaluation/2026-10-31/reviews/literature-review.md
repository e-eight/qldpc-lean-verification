# Independent literature review

## Verdict and scope

No blocking mathematical or attribution errors in the finished targeted audit. Its proposed sector adapter follows from explicit pairing and coverage hypotheses. The cited papers do not automatically supply successful certificates, a new distance bound, or a novelty claim.

Reviewed source identities:

| File, relative to the dated record | SHA-256 |
| --- | --- |
| `literature/audit.md` | `1d3a308218f85de10df1c0c84b3bf84bb77e69d4b9c6609cc58b8718fdb70be2` |
| `literature/sources.json` | `ef8a5893f0bc348b8366ff2d358607ca6825b6abf140b6eb1e1fb9105b2ff012` |

I independently inspected the relevant passages in eight primary papers. Five came from the retained TinyFish snapshots. I fetched the three seed papers through TinyFish without a new search. All three fetches succeeded at the requested URLs. The retained nine retrievals match the extraction hashes and lengths in `sources.json`. The catalog contains 27 distinct URLs, with 19 in the targeted extension. These counts include search-only results and metadata, rather than 27 full-text papers.

This review includes source inspection, exact linear-algebra reasoning, and lightweight metadata checks. It includes no numerical validation, Python test execution, Lean compilation, or independent proof of the reported detector ranks. Turing owns the separate numerical review.

## Source claims and application

[Audoux–Couvreur, Theorem 2.8 and Corollary 2.11](https://arxiv.org/html/1512.07081v3) support the overlap-counting predecessor. The full-rank and paired-basis hypotheses are explicit. The discussion permits distinct bases for the two orientations. The audit correctly separates these fixed-class statements from the proposed mixed-class adapter.

[Jochym-O'Connor–Kubica–Yoder, Lemmas 2 and 4](https://arxiv.org/html/1710.07256v1) support common-anticommutation counting and scrubbing. They use a fixed logical class and distinct representatives. The audit correctly avoids attributing multiplicity-based packing or the mixed-class adapter to that set definition.

[Bostanci–Kubica, Theorem 5](https://arxiv.org/html/2108.04738v1) identifies the fixed-class representative-weight LP optimum with the supremum of multiplicity-based disjointness, attained at finite integer capacity. The audit correctly treats exact feasible weights as certificates. A dual for a restricted list gives no obstruction for omitted representatives.

[Gottesman, Section 3.2](https://arxiv.org/html/quant-ph/9705052) supports the stabilizer and normalizer framework. The audit labels its extension, annihilator, and lower-bound monotonicity statements as deductions. Adding commuting stabilizers preserves the existing lower bound. It does not establish the stronger residual bound of seven. The warning about transporting an old upper witness is appropriate.

[Galindo–Geil–Hernando–Ruano, Theorem 3 and the relative-weight definition](https://arxiv.org/html/1610.06363) support the nested-pair sector distances and the physical-support interpretation. The residual target is `M1(Z_K,B_Z)`. The audit correctly distinguishes support unions of subspaces from weights of chosen basis vectors.

[Matsumoto, Theorem 1.1](https://arxiv.org/html/1405.0149v5) supports the stated quotient-projection and recovery criterion. The audit uses it only as bookkeeping precedent. It supplies no physical weight guarantee for an abstract logical-coordinate map.

[Cowtan–Burton, Lemma 6.7, Definition 6.8, Proposition 6.10, and Appendix F](https://arxiv.org/html/2301.13738v6) support the conditional distance-preservation discussion. The audit retains the logical-dimension condition and the separate merged-Z-distance obligation. Appendix F supports the warning that a valid merge can lower distance.

[Poirson–Roffe–Booth, Definitions 2.5–2.6 and Section 4.2.2](https://arxiv.org/html/2505.01370) support the distinction between logical maps and physical weight control. The auxiliary-distance discussion is not presented as a theorem supplying the missing source bounds.

## Sector and quotient reasoning

The same-qubit formulation is correct under the stated commutation, independence, and complete-pairing assumptions. Adding fifteen independent X classes raises the X rank from 274 to 289 and leaves the Z rank at 274. The resulting encoded dimension is three. This arithmetic remains conditional on the numerical inputs.

The residual X space `H_X/U` pairs perfectly with `Ann(U)`. For any fixed nonzero residual Z class, four of the eight quotient classes pair to one. Mixing within one quotient class is ordinary fixed-class packing after extension. Mixing all compatible quotient classes requires the broader sector argument.

The optional iteration is sound with an explicit invariant: every physical logical vector below seven annihilates the current good span. Each successful conditional certificate excludes the newly detected survivors. Independence and row-plus-good-span provenance remain required at every step. The audit correctly gives no guarantee of successful packings or reduced runtime.

## Remaining limits

No revision is required before using this audit to guide the prototype and bounded experiment. Literal application still requires independent numerical checks and kernel replay. Neither the three-dimensional annihilator nor a reference vector proves its seven sector bounds.

The audit candidly records its HTML/version limitations. Two full-text endpoints are unversioned, and no publisher-PDF identity comparison ran. The bounded source search cannot establish novelty or absence of prior work. The present proved overall bounds remain `6 <= d <= 20`.
