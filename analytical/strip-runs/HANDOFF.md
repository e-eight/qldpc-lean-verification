# Local17 formal-worker handoff

2026-11-11. All mathematical claims here are **PROPOSITION, independent
review/formalization pending**. No Lean was run for this handoff. This is a
specification of the proof obligations, not a report that they are discharged.

The review source is frozen at
`analytical/strip-runs/DRAFT.typ`, SHA-256
`03ecc01626209d6745cadf6336d393b6da77eea31284c09900e8f5917b896419`.
It compiled with Typst 0.15.1 to the six-page
`/tmp/strip-runs-draft.pdf`, SHA-256
`e0cc6035e2c7d97e04cdee8ede0e55a4a47bcff481ced43b6c84ff8530281b85`.
Do not edit the source except to address review objections. The independent
local15 source remains frozen at its separately recorded hash. Subsequent
work toward twenty belongs in `analytical/notes/strip-deficits.md`, not here
or in either frozen draft.

## Exact theorem in the review source

Let `a, b : Fin 19 → Polynomial (ZMod 2)`. Each nonzero slice has degree at
most 18. This degree restriction is part of the stated finite problem but
is **unused** by the proof. Let `T` be the polynomial indeterminate and set
`t = T + T²`. Assume either one of the following systems, not both:

\[
\begin{array}{ll}
\mathrm F:&a_i=t a_{i-2}+b_{i-1}+b_{i-2}+T^2b_i,\\
\mathrm B:&t b_i=a_i+T^2a_{i-1}+T^2a_{i-2}+b_{i-2},
\end{array}
\qquad 2\le i\le18.
\]

These are polynomial identities. There is no modulus, truncation,
wraparound, or implicit equation outside indices 2 through 18.
Define `wt p = p.support.card`,
\(w_i=\operatorname{wt}(a_i)+\operatorname{wt}(b_i)\), and
\(W=\sum_iw_i\). Assume \(w_i+w_{i+1}\ge1\) for every \(0\le i<18\).
Let \(z=|\{i:w_i=0\}|\) and
\(E=\sum_{i:w_i>0}(w_i-1)\), so \(W+z=19+E\).

For F, \(\varepsilon=1\) exactly when \(w_{16}=w_{18}=0\).
For B, \(\varepsilon=1\) exactly when \(w_0=w_2=0\).
Otherwise \(\varepsilon=0\). The conclusions, written without truncated
natural-number subtraction, are

\[
E+1+\varepsilon\ge z,\qquad
W+1+\varepsilon\ge19,\qquad W\ge17.
\]

There are no charge, stabilizer, logical-nontriviality, input-recognition,
rank, or code-model hypotheses. Those belong to a separate application
bridge. In particular, B is already the reflected column recurrence;
do not substitute the original Z operator's row slices into it.

## Generic local interface

The proof also works for `Fin N`, \(N\ge3\), with equations tested exactly
for \(2\le i<N\), arbitrary finite polynomials, and adjacent nonemptiness
for \(0\le i<N-1\). This is a generic lift of the same hand argument;
the frozen source states the specialization \(N=19\).

Use F forcing order as increasing index and B forcing order as decreasing
index. The generic missing-exit indicators are

\[
\varepsilon_{\mathrm F}=\mathbf1[w_{N-3}=w_{N-1}=0],\qquad
\varepsilon_{\mathrm B}=\mathbf1[w_0=w_2=0].
\]

The generic conclusions are
\(E+1+\varepsilon\ge z\), \(W+1+\varepsilon\ge N\), and
\(W+2\ge N\). For the reviewed application instantiate \(N=19\).
No column-degree bound is required by this generic interface.

The following local lemmas supply the counting layer. Each indicated
window must lie inside the board, and only equations whose indices are
at least two may be invoked.

1. **Weight facts.** A singleton pair has one monomial block and one zero
   block. Monomial shifts preserve coefficient weight. Weight is
   subadditive. Evaluation at 1 is coefficient-weight parity. For a nonzero
   polynomial \(p\), \(\operatorname{wt}(tp)\ge2\); one proof is
   \(\operatorname{wt}(tp)=2\rho(p)\), where \(\rho\) counts consecutive
   support runs. A run-count API is optional: domain nonvanishing and
   evaluation at 1 already prove the lower bound and parity used here.

2. **Between-zero branch.** For zero slices \(r-1,r+1\), the middle is
   A-only in F and B-only in B. In F, if \(r+2<N\),
   \(a_{r+2}+T^2b_{r+2}=t a_r\). In B, if \(r\ge2\),
   \(T^2a_{r-2}+b_{r-2}=t b_r\). A nonempty middle therefore makes the
   respective target heavy. The only possible unavailable target is F
   middle \(N-2\) or B middle 1. The active-block conclusion itself still
   holds at that exceptional middle, using the tested equation at \(r+1\).

3. **Length-three gap.** For zeros \(k,k+3\) and nonempty interior,
   \(w_{k+1}+w_{k+2}\ge4\). Equations in F are
   \(u=q+T^2v,\ tp+q+v=0\); in B they are
   \(tv=u+T^2p,\ q=T^2(u+p)\). The frozen draft proves both cases,
   including the zero-block subcase by cancellation of \(1+T\).

4. **Length-four gap.** For zeros \(k,k+4\) and three occupied interiors,
   their total weight is at least four. This is the separate three-singleton
   contradiction in the draft; no stronger later research lemma is needed.

5. **Four occupied slices beside a zero.** In F, a zero at \(k\) followed
   by four occupied slices has total weight at least five on those four.
   Require \(0\le k\) and \(k+4<N\); equations used are
   \(k+2,k+3,k+4\). In B, a zero at \(R\) preceded by four occupied
   slices has the same bound, requiring \(4\le R<N\); equations used
   are \(R,R-1,R-2\). This supplies baseline excess one in every gap of
   length at least five, including gaps longer than five.

6. **Run propagation.** A maximal run of \(m\) short gaps has middle
   polynomials \(P_j=t^{j-1}P_1\ne0\) in forcing order. Middles after
   the first are heavy. An on-board exit is heavy as well, by the folded
   feed identity in item 2. The proof uses the active-block conclusions
   and the respective recurrence, not a presumed reversal symmetry.

7. **Cheap-exit classification.** With \(P\) the last middle's active
   polynomial, let \((A_i,B_i)\), \(i=0,1,2\), be three outgoing slices
   in forcing order. For F the identities are
   \[
   A_0+T^2B_0=tP,\quad A_1+T^2B_1=B_0,\quad
   A_2+T^2B_2=tA_0+B_0+B_1.
   \]
   For B they are
   \[
   T^2A_0+B_0=tP,\quad T^2A_1+B_1=T^2A_0,\quad
   T^2A_2+B_2=tB_0+A_0+T^2A_1.
   \]
   If the outgoing weights are \(2,1,1\), then \(P\) is a nonnegative
   monomial shift of \(1+T+T^2\) or \(1+T+T^2+T^3\). In particular
   \(\operatorname{wt}(P)\ge3\). Parity rules out one block choice;
   cancellation of a single branch monomial forces the two factorizations.
   This is proved separately for F and B in the source.

8. **Long-gap exit alternative.** If a short run feeds a longer gap with
   excess \(E_D\), then \(E_D\ge2\) or its terminal middle has weight
   at least three. For a gap of length three use item 3. For length at
   least four, failure of \(E_D\ge2\) and the heavy exit force weights
   \(2,1,1\) at its first three interiors; apply item 7. These windows
   automatically fit the tested range because the whole following gap fits.

## Polynomial-free counting interface

This component needs only a finite sequence of natural weights in forcing
order, with no adjacent zeros, and the following structural hypotheses:

- Every noninitial middle in a short run is heavy.
- Every on-board short-run exit target is heavy.
- Every longer gap has interior excess at least one.
- For every short run with a following longer gap, that gap has excess
  at least two or the run's terminal middle has weight at least three.

The previous local lemmas establish these hypotheses for each recurrence.
Do not add a hypothesis that incoming branch and gap-interior costs are
disjoint; they can overlap.

Let \(G\) be the number of short gaps, \(M\) the number of longer gaps,
and \(R_2\) the number of maximal short runs. For \(z\ge1\),
\(G+M=z-1\). A run of \(m\) short gaps has internal excess at least
\(m-1\). Each longer gap has excess at least one. These baselines total
\(G-R_2+M\).

To avoid implementing a literal selection of excess units, pair each run
with its unique following longer gap, when one exists. The pairs are
disjoint intervals except for zero endpoints. The following block bounds
suffice:

- Run of length \(m\) plus following longer gap: excess at least \(m+1\).
  If the gap costs two, add \(m-1\). Otherwise the terminal middle has
  at least two excess units, while at most one was reserved there, so the
  run costs at least \(m\); add the gap's one.
- Final run of length \(m\) with an on-board tail exit: its middles and
  that target cost at least \(m\) excess.
- Final run of length \(m\) with a missing exit: cost at least \(m-1\).
- Unpaired longer gap: cost at least one.

There is at most one missing exit and its count is exactly \(\varepsilon\).
Summing these disjoint blocks gives
\(E\ge G+M-\varepsilon=z-1-\varepsilon\).
Handle \(z=0\) separately by \(W\ge N\). This yields the natural-number
conclusions above, using \(W+z=N+E\), without accidental truncated-subtraction
arguments. A run ending at oriented zero \(N-2\) still has a target at
\(N-1\); lack of a later zero is not a missing exit.

## Application boundary and validation obligations

The physical application must separately supply the correct recurrence,
coefficient-to-physical-weight equality, adjacent nonemptiness, and the
reflection/block permutation for the original Z sector. The local theorem
does not supply charge completeness. Its specialization to nontrivial
logical classes therefore retains those external dependencies.

The current author performed hand checking, Typst compilation, and visual
inspection, not Lean verification. Any future Lean replay must follow the
repository's detached-allocation, memory/swap-limit, axiom-audit, and source-hash
requirements. The reviewer and formal-worker tasks are independent of the
ongoing research toward twenty.
