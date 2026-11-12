# Independent review of the analytic instance lattice bounds

Reviewed source: `lattice-draft.md`, SHA-256 `e62b15092815a311817bb728348494a692f8eb38952161caa4c4180afa77f424`.

Three fresh independent agents received only the complete proof document,
without inherited conversation history, source code, numerical output,
working notes, or other reviews. Each was instructed to find a fatal flaw
and check every numeric table row by hand.

| Referee | Verdict | Scope |
| --- | --- | --- |
| `/root/integration_referee_one` | PASS | Entire proof and all18 rows |
| `/root/integration_referee_two` | PASS | Entire proof and all18 rows |
| `/root/integration_referee_three` | PASS | Entire proof and all18 rows |

Each independently verified both lattice relations and the quotient
determinant in every row, all36 strict margin products, all72 entries of
the norm quadruples, and every nonzero attaining vector. Each checked the
integral-coordinate recovery, determinant signs, inverse inequalities,
integer rounding from N<D to N≤D−1, and all nine derived coefficient pairs.
Special checks included the basis-difference minimum for262, the second
basis vector minimum for278, negative periods for454/562, composite moduli,
zero relation quotients, and both even regressions.

No mathematical objection or erroneous row was found. No objection survives.
The reviews concern the paper argument; implementation and kernel status
are separately recorded in the integration evaluation.

## Root adversarial audit

The root reread the entire proof from its main statement, including every
table. The case list follows from the strict inverse bounds and integrality;
it was not produced by a search. The explicit tables allow every fixed
calculation to be repeated by hand. Basis discovery has no proof authority.
No unresolved mathematical gap was found.

Final promotion awaits the complete instance Lean replay and dependency audits.

## Accepted formalization

The universal theorem, explicit coordinate uniqueness, six guarded targets,
all18 emitted lattice minima, all18 family parameter capstones, and both
original262/562 public entry points passed bounded replay. All20 parameter
proofs also passed body-level dependency checks requiring the new connected
shortest-relation theorem and the analytic basis bound, and excluding
finite_exclusion and stored physical wx/wz witness dependencies.

The final proof differs from the frozen reviewed draft only in acceptance
status. No mathematical statement, arithmetic table, or argument changed.

Final `PROOF.md` SHA-256: `d74858af7d52bc11537c4bd7c9fc8cbb8706a8c24490cb4ac8d8974e1d755ebd`.

> **Source format note (2026-11-12).** The final `PROOF.md` named here was later
> replaced by a LaTeX translation, `PROOF.tex`, with the same mathematical
> content. The Markdown file and the hash quoted here are in commit
> `cee205f5615f9404e1b27eafd7513604663abe95`. The reviewed draft is unchanged. `ADAPTERS.md` later changed only
> the path of the cited cyclic proof; the hash quoted here is in the same commit.

## Independent adapter reviews

The same three independent referees separately read `normalized-draft.md`
and `rectangle-draft.md`, using only the complete final cyclic-distance and
rectangle-family-distance proof documents as explicitly named dependencies.
All three returned PASS for both transfer arguments. They checked all row
shifts/species, surjective row labels including duplicates, exact index
ranges and flattenings, physical-weight preservation, and logical predicates.
The cyclic checks included m=1, a=0, loops and parallel edges; the rectangle
checks verified every range at m=n=17 and retention of the separate weight20
upper witness.

Two reviewers noted that “same rows” in the rectangle opening could mean
unordered equality. The final adapter note says “same indexed rows”; the
proof had already stated entrywise equality A'=A,B'=B with the same indices.
This wording resolves the only objection. No mathematical argument changed.
The root reread both complete transfer arguments and all referenced premises.
The implementation and actual proof paths were checked separately in Lean.

`normalized-draft.md` SHA-256: `e14ca460ef21806d4b6083fe5af3f582efbc94eaefc45bf01a55f5108ea509c3`.

`rectangle-draft.md` SHA-256: `cb3f3a3971cceb988ec191a4a4870128fb35cd9238a55de93ffdc4a664a6efe2`.

`ADAPTERS.md` SHA-256: `2ca3c7f85c84e9de45ddcc5945cf7acc70b3cd9ea266d2935f55c5ffc1b2a6fd`.
