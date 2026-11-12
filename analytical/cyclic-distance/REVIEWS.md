# Independent review record: Cyclic exact distance and rotated-square families

Reviewed document: `DRAFT.md`. SHA-256: `d4a8f7e4e6d1ecbb1ca666998b1b9368181fb7ffd0c9207f616c2f9297dcddc8`.

Three independent agents, `/root/referee_one`, `/root/referee_two`, and
`/root/referee_three`, each read the entire proof document. Each was created
without inherited conversation history and instructed to seek a fatal flaw,
read only the named proof documents, and inspect no source code, numerical
results, working notes, or other reviews. They independently reviewed the
four initial family documents; no author's reasoning was supplied.

All three returned **PASS**. No fatal flaw, named gap, mathematical objection,
or counterexample survived. Each pass concerns the paper proof only; Lean
and axiom verification are recorded separately.

Checks explicitly covered: Joint connectivity, ranks, complete binary winding detection, trail decomposition, halving shortest relations, duality, integral Gaussian coordinates, physical weights, zero steps, m=1, even periods, loops, parallel edges, and b=0.

## Objections and resolutions

Two referees noted the harmless use of L for both walk length and the
label map. The final document renames the label map to mathcal L; no
mathematical statement or argument changes. Supplemental all-components
review is recorded below once complete.

## Root adversarial audit

The root author reread the entire document from its first statement through
its conclusion, checking the main theorem against definitions, all supports,
case splits, algebraic identities, boundary conventions, and actual physical
weight. No unresolved objection remains. No enumeration or numerical
certificate supplies a proof step.

Final promotion is made only after corresponding guarded Lean replay.

## Supplemental arbitrary-component theorem

Reviewed supplement: `COMPONENTS-DRAFT.md`, SHA-256 `dcc9a525db7f8e33e5b1c1c154dc20ef6998780616c1b7d20ac724e7b8a3601b`.
Each of the same three independent referees read the entire supplement,
using only the previously reviewed connected proof as precursor. All three
returned PASS with no mathematical objection. They checked the explicit
vertex/edge inverse, every block row, all component logicals, exact physical
weight addition, integer divisibility cancellation, c=1, m=1, s=t=0, one
zero step, both steps divisible by m, parallel edges, and even c.

One referee requested disambiguation of section numbers and the locally
reused symbol c on integration. The final document uses labelled Parts I/II
and explicitly states each symbol scope. Every precursor reference names
Part I. The author reread both complete arguments and their integration.
The final mathematical text consists of the two reviewed proofs; status,
notation, introductory statement, and cross-references are the only edits.

Final artifact: `PROOF.md`, SHA-256 `0b3a4309547352e4333b95e96a4ea38653e07792d83d09bbbeff64c180655928`.
