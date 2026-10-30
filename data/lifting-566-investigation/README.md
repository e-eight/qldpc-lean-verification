# Applicability of elementary qubit removal to code566-18-20

The actual submitted 566 matrices admit a reconstructed **12-step elementary
removal certificate** from the actual 578 matrices: six X removals followed by
six Z removals of weight-1 stabilizers. The final matrices match literally,
including row order. This is an exact Python linear-algebra result, not a new
kernel proof and not a reconstruction of the missing random-search history.

Upstream revision: [8c87413d16b78cdd934b7b7a8592cddc81ae6eed](https://github.com/unitaryfoundation/qldpc-challenge/tree/8c87413d16b78cdd934b7b7a8592cddc81ae6eed).
This investigation follows the kernel-checked small-example gate documented in
the [lifting record](../lifting-evaluation/); it runs no Lean jobs.
All indices below are zero based.

| Input | n | X rows/rank | Z rows/rank | k | Stored logical witnesses |
|---|---:|---:|---:|---:|---|
| `codes/578-18-20.json` | 578 | 280/280 | 280/280 | 18 | X: 20, Z: 21 |
| `codes/566-18-20.json` | 566 | 274/274 | 274/274 | 18 | X: 20, Z: 21 |

Every witness has the stated weight, zero opposite-check syndrome, and lies
outside its own stabilizer row space. These establish upper bounds only.
CSS commutation and maximum check weight 8 are checked for both inputs.

The raw SHA-256 hashes are:

- 578 JSON: `440bc07c8756e79f98dfbd6fb09401a1b78f9ba11182f4ac44b28a4b03a4f514`
- 566 JSON: `061a2b4347de9e023c6ac143503ba67d09cd6614d2b5c210f1a5a17f99de67be`

`assessment.json` also hashes both notes, `boundary_engine.py`, both local
QubitRemoval Lean files, and the generator itself. It checks that these files
did not change during the run. The note for 722 is context only; no relation
between 722 and these matrices is asserted. The boundary engine was read,
but was not imported or used to generate a potentially different source.

The layouts have unique coordinates, and every final coordinate matches a
source coordinate exactly as a parsed number; no tolerance or geometric
guessing is needed. The retained coordinate order is the source order with
`272..277` and `564..569` deleted. The complete 566-to-578 map is in the JSON.

| Pair i | Source coordinates (a_i,b_i) | Source X row | Source Z pair row | r_i in final coordinates |
|---:|---|---:|---:|---|
| 0 | (272,564) | 182 | 201 | 221,224,257,505,522,538 |
| 1 | (273,565) | 183 | 207 | 222,225,258,506,523,539 |
| 2 | (274,566) | 184 | 213 | 223,226,259,507,524,540 |
| 3 | (275,567) | 185 | 219 | 224,227,260,508,525,541 |
| 4 | (276,568) | 186 | 225 | 225,228,261,509,526,542 |
| 5 | (277,569) | 187 | 231 | 226,229,262,510,527,543 |

Each distinguished source X row is `r_i + e_a_i + e_b_i`. No other source X
row meets either coordinate of that pair. Each distinguished Z row is exactly
`e_a_i + e_b_i`. Deleting these six X rows, these six Z rows, and the twelve
columns reproduces every final sparse row in order. Thus recognition here is
stronger than equality of parameters or abstract code equivalence.

For the chosen elementary sequence, first remove `a_0,...,a_5` as X pivots.
Each X pivot has a seven-bit fan: its six retained bits and its partner b_i.
The remaining X rows already have zero in the pivot column. For every Z row,
its old pivot entry equals its retained dot product with this fan, exactly
the graph condition in `old(C,s)`. After these six steps, each distinguished
Z pair row has become the weight-1 check `e_b_i`. Remove `b_0,...,b_5` as
Z pivots, clearing their columns in other Z rows first. These six cleanups
have zero fan. The first six current coordinate indices are all 272; the
last six are all 558. Each rank shift, commutation relation, graph condition,
and resulting k is checked. The JSON records pivot rows, supports, cleared
rows, coordinate-order hashes, and intermediate row-space hashes. Intermediate
codes in this certificate are newly reconstructed, not attributed to upstream.

The upstream note's “ten accepted moves” cannot be the count of elementary
one-coordinate removals from 578 to 566. No original trace was committed.
The certificate above establishes an available legal sequence without trying
to reconcile the historical count or infer which moves were accepted.

**Mathematical derivation (not formalized):** let U,V be orthogonal CSS row
spaces, and let pi delete coordinate q. An X removal with any pivot S in U
having S_q=1 produces `pi(U intersect {u_q=0})` and `pi(V)`. Clearing q in a
basis spans exactly the first kernel; orthogonality determines the deleted
V entry by the pivot parity. The first rank drops by one, and pi is injective
on V because `e_q` cannot belong to V. This proves that the resulting row
spaces do not depend on the pivot S. The dual statement exchanges U and V.

For disjoint typed deletion sets D_X,D_Z, iterating this identity gives

```
U_final = pi_D(U intersect {u restricted to D_X = 0})
V_final = pi_D(V intersect {v restricted to D_Z = 0}),  D = D_X union D_Z.
```

Shortening and puncturing distinct coordinates commute as operations on
subspaces. If the restrictions `U -> F2^D_X` and `V -> F2^D_Z` are both
surjective, every ordering has an available pivot at each step and gives
these same spaces. This is a useful general certificate criterion; it does
not assert that the resulting code has preserved distance. Pivot choices
can change the logical lifts and the strength of their weight bounds.

**Checked finite identities:** all 64 choices of one coordinate from each
pair as X, and the other as Z, have both restriction ranks 6 and produce
the final row spaces. For these twelve coordinates they are the only possible
typed partitions for a k-preserving elementary sequence ending at the final
ranks: six X deletions are necessary, and the six paired, identical X column
restrictions force exactly one from each pair. In the displayed sequence,
each of the twelve pivots was also replaced by its sum with another same-type
row having zero pivot entry; all resulting spaces were unchanged. No logical
representatives were enumerated.

Explicit composite maps are also available. Write K for retained coordinates
and `R(z) = (r_i dot z)_i`. A final X cycle lifts by zero padding on all pairs.
An old X cycle has equal entries `t_i` on a_i and b_i, and decodes to
`x_K + sum_i t_i r_i`. A final Z cycle lifts with a_i entry `r_i dot z`
and b_i entry zero; an old Z cycle projects to K. The pair Z stabilizers
generate the kernel of Z projection. The distinguished X rows generate the
kernel of X decoding. The script checks the cycle and stabilizer images
on bases, with cycle dimensions 298 -> 292 on both sides and induced logical
quotient dimensions 18. These maps preserve the X/Z logical pairing.

**Mathematical derivation (not formalized):** these decompositions give

```
dX_source = min_{x final X logical, t in F2^6}
              wt(x + sum_i t_i r_i) + 2 wt(t)
dZ_source = min_{z final Z logical} wt(z) + wt(R(z)).
```

For X, the equal pair bits cost two each. For Z, the required parity within
each pair costs zero or one, and adding its pair stabilizer permits either
placement. Nontriviality follows from the checked stabilizer/kernel
decompositions. These are derivations from the finite identities, not computed
distance minima or new Lean theorems. In particular, R has rank six even on
the final Z stabilizers. Parities can change within one logical class, so a
test of a chosen logical basis would not certify the relevant minimum.

The existing `new_X_lower`, `new_Z_lower`, `old_Z_lower`, and
`distance_comparison` theorems apply stepwise after formal row-space and
permutation transport, using CSS duality for Z pivots. Each zero-fan cleanup
preserves both distances exactly. The resulting useful bounds are

```
dX_final >= dX_source
dZ_final <= dZ_source <= dZ_final + 6.
```

If a genuine source lower bound `dX,dZ >= 20` were supplied, these yield
`dX_final >= 20, dZ_final >= 14`, hence only `d_final >= 14`. Together with
the stored X witness, this would make final dX exactly 20. No such source
lower bound was supplied by the upstream notes or inputs. The existing
`distZ_preserved_iff` assumes the new minimum; it cannot manufacture a new
distance lower bound from a zero-parity witness alone.

To prove final d=20, one still needs lower bounds of 20 on both final sides.
One possible route is a source lower bound plus an actual Z no-loss argument.
Under a source Z lower bound of 20, the block formula rules out final Z
logicals of weight below 14 automatically. What remains is to exclude final
Z logicals z with `14 <= wt(z) <= 19` and `wt(z)+wt(R(z)) >= 20`.
No claim is made that these residual obligations are easy. Direct final
lower bounds are another route. No conjecture about d=20 is validated here.

The recommended next proof obligation is a recognition/transport theorem:
equality of CSS row spaces and a permutation of physical coordinates should
transport the literal `old(C,s)` logical and weight statements to submitted
matrices. Add the dual operation and compose the twelve certified steps.
This converts the reconstructed certificate into a kernel statement about
these inputs; the Z distance obligation remains separate. No novelty claim
is made for the shortening/puncturing facts or block formulas.

Reproduce with Python 3.13, from the repository root:

```bash
setsid --wait timeout --signal=TERM --kill-after=2s 120s \
  python3.13 data/lifting-566-investigation/investigate.py
setsid --wait timeout --signal=TERM --kill-after=2s 120s \
  python3.13 data/lifting-566-investigation/investigate.py --check
```

The standard-library-only script enforces 1 GiB address space, 120 CPU seconds,
and a 120-second wall alarm. `--check` verifies byte-for-byte regeneration
without writing. `--upstream PATH` selects another clone; hashes describe
the actual raw files. Run with assertions enabled. No RIS, SAT, distance
search, Lean/lake invocation, dependency change, or upstream write occurs.
