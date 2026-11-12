# Analytic qLDPC research progress

## Current state — read this before the chronological log

THEOREM: the pinned submitted722 code has commuting checks, ranks357, k8,
dX>=17, 17<=dZ<=20 and 17<=dPauli<=20. The complete final hand proof and PDF
are `analytical/rectangle722-submitted/PROOF.typ` and `PROOF.pdf`. Three
independent document-only hostile referees accepted it; the author reread the
entire original source and its rendering. The current33-page restructuring
has three additional clean document-only reviews and complete layout checks. All final Lean capstones and focused
axiom audits pass. Exact20 remains CONJECTURE, not a completed result.

Other THEOREM artifacts: symbolic lattice562 minimum23, small-support column
criterion, model722 ranks/charges, local strip15/17 and model distance15/17.
See `analytical/README.md` and source-hashed records under
`data/analytical-evaluation/2026-11-11/`. Earlier statuses below are chronological
history, superseded by later entries and this current-state summary.

Active approach families:

| Family | Current owner | Exact remaining obligation |
| --- | --- | --- |
| Strip recurrence / surplus | Mendel | Boundary and initialtail constraints for weight17–19 |
| Valuation / local transport | Ampere | Exact excess2 incoming-gap classification |
| Charge factor / hypergraph cuts | Erdos | Residual one/two-center bridge layers |
| Minimum circuit / stabilizer cleaning | Hooke | Remove repeated-center bridges without increasing weight |
| Independent adversarial checking | Goodall | First review of new local Props22–26 passed; further reviews/Lean pending |

New claims outside final proof files remain PROPOSITION. No lower20 proof exists.
The 566 and parent578 transfer routes remain blocked at explicitly named
finite-boundary/correction lemmas; no new566 result is claimed.

Validation:46 focused Python tests and repository lint/format pass; full Python
suite passes:310 passed,2 skipped in51.89s. Full package Lean audit is pending inherited cache restoration;
all new result dependency closures and guards pass. Legacy batch3 completed all16 modules successfully under
5GiB/128MiB/one thread,1800s wall and1740s CPU limits. In total35 inherited
modules are restored;234 remain absent from the umbrella closure. No legacy
replay is currently running. Private state is `.local/analytical/legacy-third-v1.*`.
Never run uncapped foreground Lean.

## Mission and acceptance criteria

Develop hand-checkable analytic certification/bounds for the project's codes and
formalize the results in Lean. Final proof documents live at
`analytical/<result>/PROOF.typ`. Each needs three independent hostile referees,
resolved objections, an adversarial self-audit, and guarded Lean axiom audits.
No numerical certificates or exhaustive machine searches may bear the analytic
argument. Checkpoints do not complete the mission.

## Initial state — 2026-11-11

Repository documentation reports nineteen exact submitted instances and bounds
7 <= d <= 20 for 566-18-20. These are inherited records, not newly reviewed claims.
The latter lower bound uses computational certificates and is not an analytic
solution under this mission. 722-8-20 also remains a target.

The worktree already contains substantial modified and untracked irreducible-search
work. Preserve it, including existing umbrella/audit edits. Do not edit archive/.
Lean runs must be detached with enforced memory and swap caps and one local thread.

## Approach registry

| Family | Owner | State and concrete next output |
| --- | --- | --- |
| Geometric homology and boundary systoles | Gibbs | Independent derivation from target construction; lemma or counterexample |
| Polynomial/module and product structure | Averroes | Independent algebraic derivation; explicit equations and exact gaps |
| Qubit removal and stabilizer correction | Hubble | Analytic correction lemma with target hypotheses exposed |
| Lattice separation by short dual coordinates | Orchestrator | Replace finite exclusion with symbolic inequalities; assess family reach |

## Claim grades

- PROPOSITION L1: the 562 lattice `7u + 145v = 0 mod 281` has shortest
  nonzero L1 norm 23 by a symbolic basis argument. Outstanding obligations:
  derive the basis, prove separation, independent review, Lean replay.
- CONJECTURE T566: the literal 566 code has distance 20. No new lower-bound
  proof is asserted.
- CONJECTURE T722: the literal 722 code has distance 20. No new lower-bound
  proof is asserted.

## Decisions and reasons

- Launch independent approaches before cross-pollination, to avoid a shared
  unproved crux.
- Inspect and improve structural arithmetic in parallel: the current 562 proof
  excludes a 45-by-45 window by kernel computation. A symbolic replacement would
  remove that load-bearing enumeration, but would remain a checkpoint.
- Keep draft results graded PROPOSITION until their proof and review obligations
  close; final PROOF.typ documents must contain only THEOREM-grade claims.

## Adversarial checklist

- Distinguish stabilizers from nontrivial logical cycles.
- Prove physical Hamming-weight control, not just algebraic equivalence.
- A source-distance hypothesis is not a source-distance proof.
- Logical-basis checks do not cover all logical representatives.
- Prove case lists exhaustive without program generation.
- Distinguish a lattice separation lemma from a complete submitted-code theorem.

## Next actions

Derive symbolic lattice separation, collect independent routes, select concrete
proofs for formalization, then commission document-only hostile reviews. Record
all gaps, counterexamples, hashes, resource caps, and review resolutions here or
in linked result records as they arise.

## Checkpoint 1 — symbolic lattice separation

- PROPOSITION L1 now has a complete written proof and a successful Lean replay.
  `Lattice/Analytic562.lean` and `Analytic562Audit.lean` passed with six guarded
  axiom checks. Four results use only propext/Classical.choice/Quot.sound;
  determinant and explicit witness use no axioms. Three independent document-only
  referees found no fatal flaw. Precision objections were fixed; two final
  rereviews have passed, the third final rereview remains pending.
- The proof derives the basis (9,-14),(13,11), bounds each coefficient in
  {-1,0,1}, and explicitly lists all nine derived cases. It replaces a 45-by-45
  finite search by pen-and-paper arithmetic. See `analytical/lattice562/DRAFT.typ`
  and `REVIEWS.md`.
- Integration changed `Lattice/Arithmetic562.lean` so both its separation result
  and compatibility finite-window theorem derive symbolically from L1.
  Replay of that module, `Bicycle562`, and `BicycleAudit` is in progress.
- Local verification uses the retained pinned 4.30.0-rc2 toolchain, detached
  systemd services, 5 GiB memory, 128 MiB swap, one Lean thread and one CPU.
  Initial launcher attempts failed due to a missing timing executable and tried
  elan provisioning; the successful run used the installed toolchain directly.
  Raw logs remain under ignored `.local/analytical/`.

## Portfolio findings and next mechanisms

- PROPOSITION G722: explicit planar 722 construction has independent X/Z checks
  (357 each), commutation and k=8 by polynomial recurrence. Independent review and
  Lean formalization are pending. Gibbs is writing a self-contained draft;
  Linnaeus owns `Planar/BoundaryRecurrence.lean` and its focused audit.
- PROPOSITION G722-bulk: full-plane syzygy exactness reduces nontrivial logicals
  to boundary charge classes. The missing weight inequality is theorem-strength;
  this reduction is not near-completion evidence. See `analytical/notes/geometry.md`.
- FALSE G722-outer-edge: all logicals must touch both outermost edges. Explicit
  counterexamples are recorded in the geometry note; two-cell boundary strips
  cannot be replaced by outermost rows.
- PROPOSITION R566: exact block lifts and a threshold-sensitive stabilizer
  correction criterion. Source lower bounds and universal correction overlap
  remain missing. See `analytical/notes/lifting.md`.
- FALSE R566-parity-only: surjectivity of the stabilizer parity map implies
  distance preservation. The lifting note records a three-qubit counterexample.
  A new investigation asks what odd-weight repair generators imply for
  weight-19 coset minima, rather than repeating the surjectivity reduction.
- Algebra route remains independent and active.

### Lattice checkpoint accepted

THEOREM L1: the nonzero integer lattice `281 | 7u + 145v` has minimum L1
norm 23. All three revised-document referee verdicts pass with no surviving
objections. Full adversarial author rereading passed. The final
`analytical/lattice562/PROOF.typ` contains the complete self-contained proof;
the reviewed draft and objection resolutions are retained beside it.
Seven Lean guards pass, including the added existence-and-uniqueness basis
theorem. The existing `Bicycle562` capstone and `BicycleAudit` passed after the
arithmetic substitution. Hashes, resource limits and timing scopes are recorded
in `data/analytical-evaluation/2026-11-11/lattice562.json`.

PROPOSITION A722-small: the algebra route derives a complete symbolic
classification of weight-one and weight-two cycles in the 722 construction;
all are zero or stabilizers. Independent review, concrete matrix adapter and
Lean verification remain open. Curie is implementing a reusable small-support
CSS lemma in `Planar/SmallSupport.lean`; this does not by itself close the
722 application. The algebra route is now seeking a genuinely new strip-weight
invariant rather than relabeling relative exactness below twenty.

No new exact submitted instance, analytic distance-20 bound, or mission completion
is claimed by these checkpoints. Notes are being normalized to the required
four-grade scheme; legacy agent A/B/C/F labels must not be read as THEOREM.

## Checkpoint 2 — boundary algebra and small supports

- `Planar/BoundaryRecurrence.lean` and `BoundaryRecurrenceAudit.lean` passed
  bounded replay (6.964s and 2.790s; reported process peak 3,786,808 KiB).
  This proves injectivity of finite scalar anchor arrays into polynomial-valued
  slices. Finite physical projection and ranks are being added by Linnaeus;
  no complete matrix-rank formalization is claimed yet.
- `Planar/SmallSupport.lean` and `PlanarSmallSupportAudit.lean` passed bounded
  replay (3.841s and 2.807s; process peak 3,774,580 KiB). The first attempt
  exposed an unavailable import and was corrected. The theorem is conditional
  on nonzero columns and stabilizer-valued two-column collisions; it supplies
  both sector bounds and QECLean's mixed-Pauli bound. Its self-contained draft
  is `analytical/small-support/DRAFT.typ`, still awaiting three referees.
- `analytical/planar722/DRAFT.typ` now states only the explicit rectangular
  model, commutation, both ranks357, and quotient dimension8. One referee
  accepted the mathematics but required removing implied graph planarity and
  unsupported external input/witness assertions. These have been removed.
  Two other independent document-only referees are active. New commutation
  formalization is owned by Socrates in `Planar/Commutation.lean`.
- Unforced A-only X cycles have a proposed sharp weight lower bound29.
  This is PROPOSITION, not a bound for mixed-block logicals. Full derivation
  remains in `analytical/planar722/RESEARCH.typ`; no final PROOF issued.

## New route: conserved cut charges

PROPOSITION A722-charge: a low boundary syndrome class in R/(f,g) is conserved
across all two-row cuts, is zero on stabilizers, and if nonzero forces weight
at least9. Dual column statement proposed as well. See algebra notes.
CONJECTURE CC-X/CC-Z: this charge detects all logicals; not yet proved/reviewed.
The proposed next mechanism is a dimension-and-surjectivity argument, not a
weight enumeration: full syndrome image has dimension76 inside 84 boundary
coordinates; total residue has rank8 if low/high strips each span the degree8
charge algebra. Equality of kernels could then prove charge completeness.
Averroes is attacking this mechanism against the explicit recurrences.

FALSE: nonzero charge forces one occupied qubit in every row. The explicit
A-only weight29 cycle occupies only odd rows and has nonzero charge. Thus
an outer-edge surcharge or one-row counting argument cannot supply twenty.

The 566 parity-repair family is blocked at a precise geometric condition:
weight19 coset minima need equal-weight zero-parity representatives. Neither
parity surjectivity nor odd-generator information forces them; explicit
counterexamples and signed-overlap conditions are retained in lifting.md.
Reassign this family only with a new cycle-equation/overlap mechanism.

## Checkpoint 3 — complete column criterion and proposed bound nine

THEOREM S2: the generic column criterion excludes all nontrivial logicals of
weight at most two, including mixed Pauli operators under both sector hypotheses.
Three document-only hostile reviews passed. Final self-audit and rendered-page
inspection passed. The final document is `analytical/small-support/PROOF.typ`;
reviewed draft and review record are retained. Source hashes and bounded replay
are in `data/analytical-evaluation/2026-11-11/small-support.json`.

PROPOSITION P722: all three independent final reviews of the explicit rectangular
722 commutation/rank/quotient document pass. Finite physical synthesis injectivity
and ranks have now passed Lean with their audit (11.284s +2.997s, process peak
3,806,096 KiB). The actual sparse-matrix correspondence and commutation capstone
remain under elaboration; this is why no final planar722/PROOF.typ exists yet.

PROPOSITION C722-9: the dimension-and-surjectivity mechanism closes the proposed
charge-completeness gap on paper and gives both sector lower bounds nine. The
charge algebra also has the y-presentation F2[y]/(1+y+y²+y⁶+y⁸); both boundary
strips span it. The full syndrome image has dimension76 and equals the kernel
of total residue on84 boundary coordinates. Thus the low charge is onto the
eight-dimensional algebra and its kernel has exactly the stabilizer dimension.
All these claims still require independent review and concrete Lean bridges.
Averroes is writing `analytical/charge722/DRAFT.typ` as a fully self-contained
proof; no claim is promoted to THEOREM and no literal-input bound is asserted.

The generic dimension-completeness helpers `Planar/BoundaryCharge.lean` passed
Lean. Its five guarded targets now pass after two expectations were corrected
to the smaller actual axiom set [propext, Quot.sound]. The concrete bulk-syzygy
kernel is being formalized by Linnaeus in `Planar/BulkExactness.lean`.
An elementary monic quadratic-division proof avoids needing a UFD citation in
the hand document. The determinant/quotient arithmetic script in
`analytical/notes/algebra_check.py` passed under Python3.13, as did Ruff lint and
format checking. It performs only explicitly stated polynomial manipulations.

## Live handoff state (continue, do not restart)

Current active ownership:

- Averroes `01a1cb85-8184-7a02-92a2-d04284e81fb3`: complete self-contained
  `analytical/charge722/DRAFT.typ`, algebra notes/check script. Main bound9 draft
  exists and compiles; first hostile reviewer has been launched.
- Linnaeus `01a1cb8b-179b-7011-9ad9-479fa88ef88e`: checked recurrence/physical
  projection completed; now `Planar/BulkExactness.lean` plus audit, monic-division
  syzygy and square-support bridge. New source exists, awaiting capped replay.
- Socrates `01a1cb90-f082-7263-ab53-274801045600`: `Planar/Commutation.lean`,
  `Planar/Parameters722.lean`, their audits. Matrix/synthesis correspondence
  and ranks/quotient capstone drafted. Commutation replay is stuck elaborating
  the symbolic convolution lemma; latest live unit `qldpc-planar-parameters-v2`
  has 2,000,000 scoped heartbeats, 100000 recursion depth, 600s wall limit.
  Suggested replacing metavariable arguments to finite_overlap by explicit
  lattice points to avoid unfolding finite sums during type inference.
- Noether `01a1cb98-cb4a-7173-a6e6-8d974f221fbf`: `Planar/ChargeAlgebra.lean`
  and audit, actual degree8 quotient with units and both x/y power bases.
  Draft source exists, awaiting capped replay.
- Mendel `01a1cb9a-114e-7193-bc7a-f5549a29fcb2`: new independent local
  cancellation/strip-deficit mechanism, only `analytical/notes/strip-deficits.md`.
- Poincare `01a1cb9c-83e7-73a3-9b38-d46559f6aa2e`: first hostile reviewer
  of charge722/DRAFT.typ only; no other context/files permitted.

Root-owned new generic helpers: BoundaryCharge and PhysicalBands. The first
passes its five axiom guards. PhysicalBands disjoint-label/row/column results
passed (3.321s +3.116s; process peak3,767,236 KiB). Added afterwards:
`adjacent_pair_bound` and its rounded endpoint strengthening, still need replay.

Use `.local/analytical/check-modules.py LABEL MODULE...` from a detached
systemd-run service to replay modules sequentially. It uses the installed pinned
toolchain, LEAN_NUM_THREADS=1, writes raw logs/exit/JSON under ignored .local.
Every service must enforce MemoryMax=5G, MemorySwapMax=128M, CPUQuota=100%,
RuntimeMaxSec=300 or600, LimitCPU=280 or560. Access to user systemd requires
the already-approved sandbox escalation; normal filesystem reads/writes do not.
Do not launch overlapping heavy Lean checks blindly. Never run unbounded Lean.

Next critical steps: finish commutation/matrix parameter replay; compile bulk
exactness and charge algebra; get all three document-only charge referees;
integrate the finite syndrome/kernel/charge maps and band-detection adapter.
The generic lemmas alone do NOT establish the concrete lower bound9.
Do not promote charge722 or planar722 to PROOF.typ before their full Lean
capstones, guarded audits, reviews and final adversarial rereading pass.

## Further live progress — 2026-11-11

- All THREE document-only hostile reviews of charge722/DRAFT.typ pass with no
  mathematical objection. See its FREEZE.sha256 and REVIEWS.md. The proof remains
  PROPOSITION until concrete Lean integration and author final audit finish.
- BulkExactness + audit PASS in components-v2 (6.806s/2.870s); both coordinate
  power bases and all quotient identities in ChargeAlgebra + audit PASS
  (7.913s/2.789s). The nine-check symbolic script is persisted and passes Python,
  Ruff lint and format checks. It uses only stated polynomial expansions.
- Commutation + audit PASS in parameters-v4 (4.114s/2.872s). A costly concrete
  sum elaboration was replaced by a generic finite-sum lemma; no enumeration
  was introduced. Actual Parameters722 is down to one reflected-impulse equality
  orientation fix. After it passes, root's Rectangle722.lean embeds the model
  in the existing QECLean-backed Input.CSSCode with physical permutations.
- CutCharge + audit PASS in components-v3-2 (4.813s/2.743s). It proves row/column
  gap=>zero charge for quadratic generators, without square-support hypotheses.
- BoundaryResidue + audit PASS in components-v3-4 (12.320s/2.906s). The concrete
  42+42 boundary coordinate maps are onto and total kernel dimension is76.
- PhysicalBands endpoint/rounding extension + audit PASS in bands-v2
  (3.427s/2.820s), including the strengthened endpoint bound in the charge draft.
- Syndrome722's physical encode/decode and kernel289 bridge exists. Its last
  replay had only a docstring/set_option placement parser error; that fix is
  assigned to Averroes. Do not treat an errored replay as a successful capstone.

Current next assignments:

- Noether additionally owns BoundaryPolynomial: encode/extract boundary84
  polynomials, support inverse, and correspondence with total/low residues.
- Averroes additionally owns SyndromeMatrix722: actual matrix syndrome equals
  tested polynomial coefficients, plus explicit reflected Z adapter.
- Socrates additionally owns StabilizerCharge722: zero low charge of all actual
  check rows. Simplified analytic mechanism: every check is a cycle supported
  in at most three consecutive strips, so it has an empty endpoint pair; apply
  the already checked cut-gap lemma. Avoid expanding hundreds of generators.
- Beauvoir `01a1cba0-573e-7310-ad65-cb79f8cfd95a` owns checked CutCharge and is
  available for integration fixes.

PROPOSITION SD15: the strip-deficit route now derives BOTH sector bounds15
from their respective recurrences plus adjacent-strip nonemptiness, using
local cancellation lemmas and gap counting. This is not yet refereed or formal.
It improves earlier PROPOSITION13/14 checkpoints; nothing is promoted on that
basis. Mendel owns analytical/strip-deficits/DRAFT.typ and strip-deficits notes.
Root supplied a candidate four-singletons-after-zero obstruction, which Mendel
proved separately in X forward and Z backward recurrences. The resulting count
is 6E>=6z-28, hence6W>=86 and integer W>=15. New route investigates paired-gap
overlap, especially length2 followed length4, instead of reweighting known
scalar constraints. Distance20 remains CONJECTURE.

Private runner now includes check-groups.py LABEL MODULE,AUDIT ...: sequential
groups under one capped service, stopping each failed group but continuing
independent groups. Latest completed allocation components-v4: Parameters722
failed only iff orientation; Syndrome722 failed only parser placement. Those
two fixes are queued. Never import failed olean outputs as verified.

## Rank theorem finalized; current distance integration

THEOREM P722 now complete: `analytical/planar722/PROOF.typ` states the main
theorem first, proves commutation, both ranks357, and binary quotient dimension8
for the explicitly defined rectangular matrices. Three reviews and adversarial
author rereading passed; all three rendered pages inspected. No external JSON
identity or distance claim is included. Main capstone `Planar.Parameters722.parameters722`
and audit passed (18.466s/2.948s). QECLean-backed `Rectangle722` adapter and its
five guards passed (3.946s/3.006s). Hashes/resources: planar722.json in the dated
analytical evaluation directory. The final proof also expands the minimum-exponent
argument explicitly instead of referring to a similar argument.

Syndrome722 and audit now PASS (8.484s/2.836s): actual finite physical full-syndrome
kernel has dimension289. CycleSpaces722 and its audit also PASS, covering both
cycle dimensions365 and both embedded boundary dimensions357.

Root has drafted (NOT YET COMPILED) BoundaryRealization, ChargeCompleteness722,
Planar/Distance722, Rectangle722Distance and focused audits. These assemble the
physical syndrome image, charge kernels, nine bands, and QECLean mixed-Pauli bound.
Do not mistake draft theorem declarations for a successful final distance proof.
They await the following concrete bridge replays:

- BoundaryPolynomial: first timeout fixed with controlled linearity simp;
  current remaining errors are explicit monomial coefficient simplifications.
  Noether owns fixes; latest failed log bridges-v2-2.log.
- SyndromeMatrix722: F2 ambiguity fixed; current remaining errors are a
  monomial coefficient case and Pi.single codomain inference/one timeout.
  Averroes owns fixes; latest failed log bridges-v2-3.log.
- StabilizerCharge722: source exists and consumes SyndromeMatrix; not yet reached
  by runner. Socrates owns it. Its proof uses empty endpoint pairs of each check.

The local strip15 DRAFT has THREE independent no-objection reviews, recorded in
analytical/strip-deficits/REVIEWS.md. No final PROOF because formalization pending.
James `01a1cbad-ebaa-73d1-8644-4addedce64e5` owns StripLocal and audit: v1 errors
are monomial-shift support/cardinality and two terminal polynomial identities.
Wegener `01a1cbad-ebc0-7cb0-8c2a-06707cae76dc` owns StripCounting and audit:
the actual successive-zero decomposition and all costs elaborate; v1 has one
backward-budget omega failure caused by syntactically unnormalized 0+1 vs1.
Latest logs strips-v1-{1,2}.log. Their source declarations remain draft until replay.

The original bulk worker and cut worker have been closed after successful checks,
freeing slots for these formalizations. Mendel continues paired-gap research in
notes; the frozen strip15 draft must stay unchanged except referee corrections.

## Complete analytic bound nine; bound fifteen capstones passed

THEOREM C722-9 is complete for the explicit rectangular matrices. Final
`analytical/charge722/PROOF.typ` is self-contained, all three hostile reviews
pass (first reviewer additionally reread the final frozen draft), author
adversarial rereading passed, and the seven-page rendering was inspected.
Concrete charge kernels/surjectivity and physical/QECLean X, Z, mixed-Pauli
capstones passed in distance-v1/v2. The dated charge722.json records the full
own-module dependency hashes, pinned manifest hash, caps, and successful checks.

THEOREM SD15 is complete as a LOCAL polynomial-array implication, not yet
promoted as the full code result: StripLocal, StripCounting, StripRecurrence
and all guards pass. Final analytical/strip-deficits/PROOF.typ has three clean
reviews and author self-audit; all four pages inspected. PhysicalStrips722 and
its audit now ALSO pass (7.645s/2.925s), linking physical weight and actual matrix
cycles to both recurrences and deriving adjacent nonemptiness from complete charge.

The actual model15 capstones have now passed Lean and guarded audits:
`Planar/Distance722Fifteen`, `Rectangle722Fifteen`, `Rectangle722FifteenAudit`
(3.264s/3.318s/3.035s). Main theorem names are Rectangle722.x_lower_fifteen,
z_lower_fifteen, pauli_lower_fifteen. The complete combined self-contained
manuscript is analytical/rectangle722-distance15/DRAFT.typ. Three referees found
no fatal flaw, but precision objections (rho overloaded as run count, k definition,
and backward reference to rank-nullity) were fixed. All three final rereviews are
pending; do not issue its PROOF.typ until those pass and author self-audit finishes.

Package umbrella and KernelAudit received additive imports/guards preserving all
preexisting edits. Full package replay could not start: 269 inherited own-package
olean dependencies are absent locally. Existing configured cluster SSH authentication
is denied; the connected server tool also cannot access servers for this account.
These are environmental limits, not failed mathematical capstones. Focused audits
of all new result dependency closures pass. Keep operational logs private. No
subscription purchase, credential change, or remote write was made.

Further research (not THEOREM): strip-runs/DRAFT.typ proves local17 on paper,
with18 except one directional edge configuration; first independent reviewer is
active. Charge-factors.md gives a distinct pure-mode>=19 route using F8/F32,
arbitrary hypergraph cuts, two disjoint paths, and exclusion of equality18.
Mixed charges and weight19 remain gaps. The degree3 parent578 investigation now
has exact opposite-orientation row formulas and an explicit18-dimensional charge
algebra, but no finite-board charge/distance bridge. These remain graded notes.

## Submitted722 bounds and final-artifact audit (latest)

The literal-input pipeline now passes: generic sparse support bridge, all714
fixed row identities, input/model equality, submitted rank/dimension and lower15
adapter, submitted lower17 adapter, explicit X23/Z20 witnesses, nontrivial pairing,
and pure-Z Pauli upper witness. Rectangle722SubmittedBounds.parameters_and_bounds
and pauli_bounds passed their guarded audit (3.250s/3.023s). No codeword search or
numerical rank certificate enters these new proofs. The source is pinned to
qldpc-challenge revision8c87413d16b78cdd934b7b7a8592cddc81ae6eed and JSON SHA256
4ab209d0c450dc7a96e6054ed29322808be87ee52eb3002c51ab4531dcc91b15.

All THREE independent full-document referees of the31-page
analytical/rectangle722-submitted/DRAFT.typ accepted the exact printed instance:
ranks357,k8,dX>=17,17<=dZ<=20,17<=dPauli<=20. They checked all714 printed rows,
all43 witness inputs and129 product terms, both cancellation multisets, and
intersection{65}. Their retained arithmetic-only scripts are now named
referee_1_check.py, referee_2_check.py, referee_3_check.py in that directory;
Ruff import/format cleanup did not change the arithmetic and all checks reran
successfully. No candidate supports or logical classes were searched.

The final PROOF.typ has been created and reread fully in four source chunks,
including every fixed support table and the complete witness proof. Root
self-audit found only an ambiguous copied local-scope sentence about 'a bound
twenty'; it was removed from DRAFT and PROOF without changing any theorem/data.
Visual QA and the submitted result's final public record are still to finish.
The final bound is17<=d<=20; exact20 is NOT claimed.

The model17 and local17 PROOF.typ files also exist. Both have three clean reviews
and passing capstones. Root reread the full model17 source (including the initially
truncated cut section separately) and inspected every changed rendered page;
pages2..6 were byte-identical to already inspected model15 pages. Exact cheap-exit
normal forms now have their own checked StripRunClassification module/audit
(4.835s/2.920s), matching the stronger named lemma in the hand proof.

Analytic check scripts were renamed to snake_case to follow AGENTS.md:
algebra_check.py, charge_algebra_check.py, charge_factors_check.py,
parent578_directional_check.py. Links/record keys were updated; final hashes
must be refreshed once artifact work finishes. Generator itself is
scripts/gen_rectangle722.py; all generated Input/Rectangle722*.lean edits must
come from it. Its46 regressions, byte regeneration, Ruff lint and format pass.

Package integration: a capped local legacy-cache pilot is now RUNNING as
qldpc-legacy-cache-pilot-v1 (5GiB memory,128MiB swap,one thread/CPU,600s wall).
Private log/JSON: .local/analytical/legacy-pilot-v1.*. It compiled missing
Input/Distance566Data in8.449s and is checking Distance566Checks0. Last observed
memory~2.9GB and CPU~69s. Seven old modules are in this pilot; no old sources
are edited. Full package still has inherited missing cache; root asynchronously
asked the user to renew configured SSH authentication while continuing locally.
Termalin AI server access is unavailable for the account; no further calls,
subscription changes, credential changes, or remote writes were made.

Active research is still separate from final THEOREM artifacts. Mendel explores
weights17..19 via surplus/run/valuation/endpoint constraints in strip-deficits.md.
Erdos explores charge-factor/hypergraph bridge layers in charge-factors.md; pure
modes and no-bridge cases have proposed20 bounds, while mixed bridge cases remain
open. Gauss independently attacked graph Propositions11–17 and found no fatal
flaw, but explicitly identified remaining one-bridge18/19 and repeated-bridge
configurations. Those research claims remain PROPOSITION, not final theorems.

## Final submitted artifact publication

THEOREM: final submitted722 proof has passed full author source rereading and
30-page rendered inspection. PROOF.pdf is included beside PROOF.typ. Three
independent hostile full-document reviews have no surviving objection. Final
capstones prove ranks357,k8,17<=d<=20; exact20 remains unproved. Public inventory
and README now distinguish this completed bound from the continuing exact20 work.

The legacy cache pilot and next batch both passed, restoring19 old modules
without source edits. Full package audit remains pending; focused new audits pass.
The umbrella and main audit now include the two final submitted bound capstones.

THEOREM artifact records now include submitted722-bounds.json, strip-runs.json
and rectangle722-distance17.json. Local17 was reread from beginning to end and
all six rendered pages inspected. The46 generator regressions and targeted
Ruff checks passed again using workspace-local UV_CACHE_DIR (the default cache
is read-only in this sandbox). No permission escalation was needed for Python.

A third detached legacy replay is running: legacy-third-v1,16 modules,
5GiB memory,128MiB swap,one CPU/thread,1800s wall/1740s CPU. Before it started
250 inherited imports lacked compiled artifacts. Private results remain under
.local/analytical. It does not change any legacy proof source.

PROPOSITION: new strip gap costs and revised surplus allocation are recorded
in strip-deficits.md Propositions22–26, with exact20 still open. Goodall is
independently attacking those claims. PROPOSITION: graph bridge centers reduce
to at most two distinct centers/four bridges in weight<20; the residual
attachment families remain unproved. None is promoted into final proof files.

Goodall (01a1cc28-97a5-7281-81b3-6e13f5be57a9) reports no surviving
mathematical objection to local strip Propositions22–26. Checked both exact
length4 forms, all4 unique-heavy positions in longer gaps, the disjoint slack
identity for (89), and dyadic packets9/15/19. Scope excludes charge completeness
and input identification. One of three required reviews only; no promotion.

Fresh tasks: Ampere owns tight-gap-transport.md (exact incoming excess2 gaps);
Hooke owns bridge-cleaning.md (stabilizer cleanup at repeated bridge centers).
Mendel focuses complementary initialtail/boundary constraints, Erdos residual
bridge attachment geometry. These are distinct mechanisms, not repeated
requests to assume a missing global distance lemma.

The retained9 analytic Python checks pass explicit-file Ruff lint/format.
Fixed submitted-row/witness checks and charge algebra diagnostics reran and pass.
Historical charge722 record corrected two renamed diagnostic paths/hashes;
no mathematical proof sources changed.

Validation checkpoint: full pytest310passed/2skipped, Ruff lint/format clean.
Third bounded legacy batch completed16/16 with exit0;35 restored in total.
Final submitted theorem unchanged; no exact20 or full-package-audit claim.

## Literature novelty audit — 2026-11-11

User requested a literature search after asking which proof tools were new.
This audit changes attribution, not the proved inequalities or Lean proofs.
Three independent search agents: Ptolemy (polynomial/bulk algebra), Hegel
(boundary charges), Epicurus (strip counting and convolutional distance).
Primary papers were read with TinyFish; missing displayed equations in HTML
were checked against the original PDF. No Lean builds or proof-source edits
were required for this literature task.

PROPOSITION N1 (evidence-based novelty classification; not a priority theorem):
The polynomial representation, the exact rectangular family, k=8, bulk
exactness, and finite-boundary logical charge are known or known
specializations. They must not be described as newly invented tools.

Direct precedents:

- Haah, *Commuting Pauli Hamiltonians as maps between free modules* (2013),
  https://arxiv.org/html/1204.1063v4 : polynomial stabilizer modules, excitation
  maps, exactness and charge sectors.
- Liang, Eberhardt, Chen, *Planar quantum low-density parity-check codes with
  open boundaries* (2025), https://arxiv.org/html/2504.08887v4 : Figure1 and
  SectionII give exactly f=x+x^2+y^2 and g=1+x^2y+x^2y^2 and the rectangular
  [[2LxLy,8,d]] family. SectionIII.2 Eq6 gives k_open=dim R/(f,g).
  Earlier versions explicitly give the basis1,y,...,y^7. AppendixA reviews
  the polynomial formalism. Small tabulated distances use integer programming;
  larger distances use probabilistic upper bounds (AppendixD).
- Breuckmann, Choe, Eberhardt, Pereira, Steffan, *Logical Operators and Derived
  Automorphisms of Tile Codes* (2025 preprint; CMP2026),
  https://arxiv.org/pdf/2511.14589 and
  https://link.springer.com/article/10.1007/s00220-026-05672-8 : Section4.2
  explicitly uses the same polynomial pair (with names interchanged).
  Section4.1 is two-generator Koszul exactness. Section4.3 Lemmas4–5 and
  Theorem3 identify finite logical cohomology with R/(f,g) by retaining the
  bottom-boundary syndrome. This is the direct precedent for our complete
  low-boundary charge, not merely a physical analogy. Theorem4 gives the
  rank count2LM-(L+D)(M-D)-(L-D)(M+D)=2D^2; D2,L=M19 yield722,357,357,8.
  Theorems assume algebraic topological order on the relevant charts; one
  cannot substitute infinite-bulk exactness alone for these hypotheses.
- Wang, Pryadko, *Algebra of Bivariate-Bicycle Surface Codes* (2026),
  https://arxiv.org/html/2606.08771v1 : Lemma1 bulk coprimality/exactness;
  Statement7 and AppendixH give general boundary-crossing lower bounds
  dX>=Ly/Delta_y,dZ>=Lx/Delta_x under explicit edge assumptions. This is
  direct precedent for the range-based support/cut argument. Exact numerical
  substitution requires mapping their size/anchor conventions.

PROPOSITION N2 (narrow possible contribution; priority unresolved): The exact
forward/backward cheap-exit classification, endpoint discount, and disjoint
excess allocation giving E>=z-1-epsilon and W>=17 have not yet been matched
in the examined sources. Elementary coefficient recurrences, binary run
counting and amortized counting are not themselves new methods. A distinct
proof of the specific inequality may be a contribution; absence of search
hits is not proof of novelty. The independent distance-comparison search is now complete; see below.

PROPOSITION N3 (formalization scope): No first-ever Lean/QEC claim is justified.
Our repository explicitly depends on Stavan-Jain/QECLean. Additional prior
work includes *End-to-End Formalization of Quantum Error Correction*,
https://arxiv.org/html/2605.16523v1 (Lean-QEC with verified SAT reductions),
and *QECert: Formal Foundations for Quantum Error-Correction Theory in Lean*,
https://arxiv.org/html/2611.05047 (3Nov2026). Potential contribution is the
specific analytic proof and pinned-input formalization, not Lean verification
of quantum codes in general.

Decision: describe our work as an elementary explicit specialization and Lean
formalization of known planar/tile-code algebra, combined with a specialized
analytic run-exit distance bound. The earlier suggestion to extend the same
polynomials to rectangles should acknowledge that the family and its logical
structure already have general theorems in the cited literature.

Technical caution for later use of the tile paper: Example2's printed
coordinate factorization/y=x^149 and Example1's Ty=Tx^150 require reconciliation
against the stated generators. The abstract F8+F32 structure and period217 are
prior art; the discrepancy does not make our charge construction new. Do not
copy the coordinate formulas without checking conventions and identities.

All three literature agents have now returned. Epicurus identifies the exact
cheap-exit lemma and the disjoint run allocation as the strongest remaining
novelty candidate, with MODERATE confidence that this argument differs from
sources examined and no established priority claim.

Additional methodological precedents:
- Hoest, Johannesson, Zigangirov, Zyablov, *Active distances for convolutional
  codes* (1999), SectionIII Theorem6, pp663 and Eqs39–41:
  https://lup.lub.lu.se/search/files/5276811/1058638.pdf . Bounds on initial,
  terminal and inter-zero-burst segments predate our accounting strategy.
  Encoder states and physical slices are different; no direct reduction to
  their theorem has been proved here.
- Johannesson, Pavlushkov, Zyablov, *Woven convolutional codes* (2005), Section2,
  https://www.jip.ru/2005/132-158.pdf : segment weights and affine active-distance
  bounds. This is a methodological precursor, not the exact epsilon formula.
- Devakul, Williamson, *Fractalizing quantum codes* (2020/2021), Section2.1,
  https://ar5iv.labs.arxiv.org/html/2009.01252 : polynomial cellular-automaton
  powers, including1+T. The shift inT+T^2 does not create a new mechanism.
- Grassl, Roetteler, *Constructions of Quantum Convolutional Codes* (2007),
  SectionII.A: polynomial checks and finite-memory recurrences are standard.

No exact match was established for local strip-runs Lemmas6–7 (cheap exit
2,1,1 implies a three-/four-term feed) and Section5's disjoint reservation
(G-R2)+M+(R2-epsilon). Nontriviality by odd pairing and explicit upper witnesses
are standard CSS arguments. The result17<=d<=20 is unchanged. None of this
literature audit establishes a first-ever result or changes the meaning of
THEOREM from correctness/refereeing into a claim of originality.

The parameterized family and boundary structure already exist in published
work. Future family formalization should specialize or formalize those known
hypotheses and focus new research on sharper weight inequalities, not claim
rediscovery of the algebraic framework as novelty.

## Contribution-first manuscript restructuring (2026-11-11)

Decision: implement the user's requested emphasis in rectangle722-submitted/
PROOF.typ while preserving its self-contained hand-proof scope. Main text:
Theorem1, attribution/route, local Theorem2, Lemmas1–7, dedicated cheap-exit
Section5, disjoint allocation Section6, and elementary physical derivation/
completion Section7. The main text is8 pages. AppendicesA–E retain all algebra,
rank/charge/cut arguments, input identification, witnesses and714 numerical rows.
Six primary sources are cited through references.bib. Priority remains qualified.

THEOREM unchanged: ranks357,k8,17<=d<=20. Six tables, seven local lemmas and the
entire disjoint counting proof are byte-identical to the previous edition.
Three new independent document-only hostile reviews (Newton,Planck,Carver)
returned no surviving objection; see REVIEWS.md. The final33-page PDF was
compiled and visually checked, with12 identical table-page bodies verified by
pixel comparison against the prior inspected rendering. Source hashes and
review history were refreshed. No Lean source or dependency changed; focused
Lean audit results remain those already recorded. Historical DRAFT.typ remains
untouched. This task introduced no new distance theorem or exact20 claim.

## AppendixD typography and label-based references (2026-11-11)

User identified plain-text mathematics in AppendixD and hardcoded references.
Converted its formula prose, barred generators, powers, coefficients, product
coordinates and residual lists to actual math mode. Fixed Typst's subscript
argument capture in H_X/H_Z row indices and a_i(y)/b_i(y),a_j(x)/b_j(x).
All internal numbered references now use labels. A native figure-counter
statement helper generates theorem/lemma numbers and captures appendix prefixes
at the target, so even forward references renumber correctly.

Compilation,18 statement-label resolutions, an insertion/renumbering probe,
reference lint and unchanged6-table/witness-tuple checks pass. AppendixD and
affected main pages were visually inspected. One independent editorial review
found two formatting issues; both resolved, final no-objection verdict. No
mathematical or Lean-source changes. Updated33-page PDF and source-hash records.

## LaTeX sources replace Typst (2026-11-11)

User request: agents handle LaTeX more reliably than Typst. Every analytical
document was translated to LaTeX with the same basename (`PROOF.tex`,
`DRAFT.tex`, `RESEARCH.tex`, `INPUT.tex`, `WITNESS.tex`), and the `.typ` files
were removed. Earlier entries in this registry name the `.typ` files that were
reviewed and frozen; those exact sources remain in commit
`fa8b57a2d87f41e04ba9b5f5c1ed62e3debf511a`, and each REVIEWS.md carries the same
pointer. The translations use amsmath, amssymb, amsthm, mathtools and hyperref,
number every display equation, and use labels for every internal reference.
Layout is the default LaTeX article class; Typst page, title, table and
proof-square styling was not carried over.
Section, statement and equation numbering matched the Typst renders; displays
that Typst left unnumbered are now numbered as well.

Content changes beyond translation, none mathematical: submitted DRAFT now calls
its witness section a section rather than an appendix, and its support tables are
a real Appendix A; small-support statements are ordinary theorem environments
under plain section headings, not all-caps statement headings;
planar722 RESEARCH sentence capitalization; lattice562 renders `mid` and
`dot(-14)` as the intended divisibility bar and product, which Typst had
printed literally. references.bib protects the capitals of Pauli and
Hamiltonians. The INPUT and WITNESS generators now emit LaTeX only, with
byte-for-byte checks; the three submitted referee scripts and the overlap note
script now read the `.tex` sources and pass unchanged. charge722/FREEZE.sha256,
charge722/DRAFT.pdf and rectangle722-submitted/PROOF.pdf were regenerated from
LaTeX (pdfLaTeX, SOURCE_DATE_EPOCH=1794355200). Lean edits are comment-only
path and manifest updates; no Lean replay was rerun. Source-hash records in the
dated evaluation list the replaced hashes under `document_revisions`.
