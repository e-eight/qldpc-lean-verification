# Packing certificates for CSS code distances

A polynomial-size certificate for a lower bound d_X ≥ L. Combined with the
board's stored witnesses (upper bounds), it can make a distance exact.
The historical Python "EXACT" results in `CHECKS_AND_RESULTS.md` use this method.
The later QECLean surface-code proof instead transfers a structural family theorem.

The overlap bound and its integer ceiling are prior work.
See [Audoux and Couvreur, Corollary 2.11 and Remarks 2.12–2.13](https://arxiv.org/html/1512.07081v3).
For weighted representatives, see [Bostanci and Kubica, Theorem 5](https://arxiv.org/abs/2108.04738).
The project's contribution is the Lean proof and certificate interface.
The active weighted theorems are in `lean/QldpcVerification/Overlap.lean`.
`lean/QldpcVerification/Coverage.lean` proves complete detector coverage from paired witnesses and a dimension bound.
`QldpcVerification.Bicycle262.parameters` applies both parts to the submitted `262-2-15` matrices.
It proves two encoded qubits and `d_X = d_Z = 15`.

## Setup and notation

- **The code.** A CSS code on n qubits with checks H_X and H_Z, where
  H_X·H_Zᵀ = 0 over GF(2).
- **X-logicals.** x ∈ ker H_Z. A logical is trivial iff x ∈ rowspace H_X. The
  classes form ker H_Z / rowspace H_X ≅ F₂^k.
- **Z-logicals.** Symmetric: z ∈ ker H_X, with classes
  ker H_X / rowspace H_Z ≅ F₂^k.
- **Distance.** d_X = min{|x| : x ∈ ker H_Z \ rowspace H_X}, d_Z symmetric, and
  d = min(d_X, d_Z).
- **Pairing.** For an X-logical x and a Z-logical z, ⟨x, z⟩ = |x ∩ z| mod 2.
  - It depends only on the classes, because rowspace H_X ⊥ ker H_X and
    rowspace H_Z ⊥ ker H_Z.
  - It is nondegenerate: if ⟨x, z⟩ = 0 for every Z-logical z, then
    x ∈ (ker H_X)^⊥ = rowspace H_X, so x is trivial.
- **Coordinates.** Fix any basis x₁…x_k of X-logical classes. Give a Z-logical
  z the coordinates b(z) = (⟨x₁,z⟩, …, ⟨x_k,z⟩), which determine its class. An
  X-logical x ≡ Σ aᵢxᵢ then has ⟨x, z⟩ = a·b(z). The scripts use exactly this,
  with bases from the repo's `gf2.logical_basis`.

## Lemma: one class, one family

Let F be a family (a multiset) of Z-logicals, all in the same nonzero class β,
with weights λ_z ≥ 0. Let c be the largest weighted coverage of any qubit:
c = max over q of Σ_{z ∈ F, q ∈ z} λ_z. Then every X-logical x with
⟨x, β⟩ = 1 has

    |x| ≥ V(F) := (Σ_z λ_z) / c.

*Proof.* Every z ∈ F has ⟨x, z⟩ = 1, so x and z share at least one qubit.
Therefore Σ λ_z ≤ Σ λ_z |x ∩ z| = Σ_{q ∈ x} Σ_{z ∋ q} λ_z ≤ c·|x|. ∎

## Theorem: assembling a certificate

Take families F₁…F_m with classes β₁…β_m and values V₁…V_m. For a nonzero
X-class α, let B(α) = max{Vᵢ : ⟨α, βᵢ⟩ = 1}. Suppose every nonzero α is covered,
meaning some βᵢ has ⟨α, βᵢ⟩ = 1. That holds exactly when the βᵢ span the class
space. Then

    d_X ≥ ⌈ min over nonzero α of B(α) ⌉ ≥ ⌈ min_i Vᵢ ⌉.

The d_Z bound mirrors this with families of X-logicals. If some α is uncovered,
the bound still holds for every covered class, but it says nothing about the
uncovered ones. The scripts report this as "class(es) uncovered".

## Ceiling: when exactness is possible

For a family in class β, c ≥ (Σ λ_z |z|)/n ≥ (Σλ)·w_β/n, where w_β is the
minimum weight in class β. Hence

    V ≤ n / w_β ≤ n / d_Z.

So the certificate can prove d_X exactly only if d_X·w_β ≤ n for the classes it
uses, and in particular only if **d_X·d_Z ≤ n**. `scripts/candidates.py` uses
ratio = d_X·d_Z/n, from the claimed values, as this necessary test. Claimed
values are upper bounds, so the true ratio can only be lower.

## Pitfall: one weighting for all classes

An earlier version used one mixed-class family and bounded every α by
Σ_{z: ⟨α,z⟩=1} λ_z / c. That is valid but weak. Averaging over the 2^k − 1
nonzero α, each z of nonzero class anticommutes with exactly 2^(k−1) of them.
So the minimum over α is at most (2^(k−1)/(2^k − 1))·Σλ, and the value is
capped near n/(2·d_Z) for large k. Per-class families, as in the theorem
above, avoid this loss.

## Instance A: disjoint lines (rotated surface and toric codes)

- **Construction.** Group the qubits into lines of the layout: rows, columns
  and both diagonals. Lines of one orientation are disjoint, so a set of
  same-class line logicals with λ = 1 has c = 1, and its value is the number of
  lines.
- **Surface code.** In the rotated L×L surface code (k = 1), the L rows are
  disjoint logicals of the one nontrivial class, and so are the L columns. This
  proves d ≥ L on each side.
- **Toric code.** In the rotated L×L toric code (k = 2), rows give one class
  and columns another, with L disjoint lines each, which again proves d ≥ L.
- **Script.** `scripts/line_check.py`. Lines, logical-ness and classes are all
  computed from the matrices; nothing is assumed about the family.

## Instance B: group orbits (two-block abelian codes)

**Setup.**
- The group is G = Z_l1 × … × Z_lr, with H_X = [A | B] and H_Z = [Bᵀ | Aᵀ] for
  A, B ∈ F₂[G], and n = 2|G|.
- Qubit i of each block is the row-major mixed-radix index of a group element.
- Translations by g ∈ G permute the qubits inside each block and preserve both
  row spaces. The scripts verify this for each generator before using it, so a
  wrong guess about the indexing fails safely.

**The family.**
- Automorphisms act linearly on classes. For a Z-logical w of class β, let
  S = {g : class(g·w) = β}, a subgroup of G.
- The S-orbit of w, with λ = 1 for each group element, is a family in class β.
- A qubit q lies in exactly |w ∩ S·q| members, where S·q is the S-coset
  through q. So c = max over the 2|G|/|S| cosets of |w ∩ coset|, and
  V = |S|/c.
- **Translates.** Translating the family by g ∈ G gives a family in class g·β
  with the same value. So every class in the G-orbit of β gets value V.
- **Best possible.** A representative of the same weight spread evenly over
  the cosets would reach V_max = |S| / ⌈|w| / (2|G|/|S|)⌉. `orbit_check.py`
  prints this as "best".

**Special case: cyclic G = Z_l with l prime > 3 and k = 2.**
- The shift acts on F₂² through GL(2,2) ≅ S₃, whose element orders are 1, 2
  and 3.
- The shift has prime order l > 3, so it acts trivially. Then S = G and
  V = l / max(|w ∩ A|, |w ∩ B|).
- A claimed d is reachable iff some representative has a largest block share
  m with ⌈l/m⌉ ≥ d.

**Limitation.** When S = G, one witness's orbit stays in its own class, so a
second class needs a second representative.

**Mixing within a class.** Translations fix the class here, so orbits of
different representatives of one class can be combined. Take an A-heavy
representative (aᵢ > bᵢ) and a B-heavy one (aⱼ < bⱼ), with orbit weights μ and
1 − μ. Then:
- the A-qubits are covered μaᵢ + (1−μ)aⱼ times and the B-qubits
  μbᵢ + (1−μ)bⱼ times;
- the two coverages are equal at μ = (bⱼ − aⱼ)/D, where D = (aᵢ − bᵢ) + (bⱼ − aⱼ);
- that gives V = |G|·D / (aᵢbⱼ − aⱼbᵢ).

Two mirrored representatives of weight w reach V = n/w, the full ceiling.
Checking every single representative and every (A-heavy, B-heavy) pair is
exact: in two dimensions, a mixture of more representatives never does better.

**Bound for k = 2.** Each nonzero opposite class anticommutes with exactly two
of the three nonzero classes. So the side bound is the ceiling of the median of
the three class values, with a class that has no representative counting as 0.
The median rule needs no class coordinates, and `verify_orbit_k2.py` uses it
that way.

**Class ceiling from block shares, for any family.** Suppose every logical in
class β has at least s qubits in block A. Then any family in class β, orbit or
not, has value at most |G|/s. Summing coverage over block A gives
Σ_{q∈A} cov(q) = Σ λ_z |z ∩ A| ≥ s·Σλ, so some A-qubit has coverage at least
s·Σλ/|G|. The same holds for block B. A class whose logicals are all lopsided
therefore caps the certificate, however long the search runs.

**Block-parity classes.** In the weight-4 two-block codes here, each circulant
polynomial has even weight. So the all-ones vectors on block A and on block B
are X-logicals. When they are independent modulo stabilizers, they form a class
basis, and a Z-logical (u, v) has class (|u| mod 2, |v| mod 2).
- Checked true for [[226,2,15]], [[454,2,21]], [[562,2,23]] and [[630,2,21]].
- Not true for [[672,2,24]], where the search reads classes from a computed
  basis instead.

## Instance C: the duality image (bicycle codes)

**The map.**
- For H_X = [A | B] and H_Z = [Bᵀ | Aᵀ], where ᵀ corresponds to g ↦ g⁻¹, the
  permutation π: (A, g) ↔ (B, g⁻¹) maps the X-check rows onto the Z-check rows.
  The scripts verify this per code before using it.
- So π maps X-logicals to Z-logicals bijectively, preserves weight and
  nontriviality, and is linear on classes.

**Lemma.** ⟨x, π(x)⟩ = 0 for every x.

*Proof.* π is a fixed-point-free involution: it swaps the blocks. So the qubits
q with both q and π(q) in x come in pairs {q, π(q)}, and their count is
even. ∎

**Consequences for k = 2.**
1. π maps an X-class α to the unique nonzero Z-class orthogonal to α. So
   π(w_X) lies in class(w_Z) exactly when the stored witnesses commute.
   - If they anticommute, π(w_X) supplies the second class for free. This is
     how [[362,2,19]] closes.
   - If they commute, π adds nothing. This was seen in all 14 such codes, as
     the lemma predicts.
2. Suppose the witnesses commute, and the w_Z family proves every covered
   X-class has weight ≥ V. Then π maps those covered X-classes onto the two
   Z-classes other than class(w_Z). So every representative of a missing
   Z-class weighs at least ⌈V⌉. That is useful for setting search targets.

## What a trusted checker must verify, per code

**Inputs.**
- The code (H_X, H_Z) and the claimed d_X, d_Z with their witnesses. The board
  already checks the witnesses.
- For each side, a list of families. A family is either an explicit list of
  representatives, or a representative together with generators of S and the
  group action.

**Checks.**
1. **Automorphisms.** Each generator used maps rowspace H_X and rowspace H_Z
   into themselves (a rank test, or explicit row-to-row images).
2. **Logicals.** Each representative is a logical of the right type:
   H_opp·z = 0.
3. **One class per family.** For an orbit family, z + g·z ∈ rowspace H_same for
   each generator g of S; induction then covers all of S. For an explicit list,
   check zᵢ + z₁ ∈ rowspace H_same. Membership can be certified by giving the
   combination of rows.
4. **Coverage.** Compute c exactly; then V = |F|/c, or the weighted version.
5. **Spanning.** Show that families with k independent classes are present:
   rank([H_same; z₁; …; z_k]) = rank(H_same) + k for one representative per
   family. Alternatively, evaluate B(α) for every nonzero α.
6. **Arithmetic.** ⌈min B(α)⌉ ≥ the claimed distance, or ≥ the lower bound
   being certified.

Every step is polynomial-time GF(2) linear algebra. In Lean, steps 1–5 are
bit-vector computations, and the soundness theorem is the lemma and theorem
above, a short double-counting argument.

## Current finite Lean interface

`CoverageCertificate S B k` accepts a cycle space `S`, its boundary subspace `B`, and `k` detectors.
For each detector, a dual witness lies in `S`.
The witnesses pair with the detectors as the identity matrix over `ZMod 2`.
Every boundary pairs to zero, and `finrank S ≤ finrank B + k`.

Lean proves that the coordinate map is onto and that its kernel is exactly `B`.
Equal coordinates therefore identify the same logical class.
Every cycle outside `B` has a nonzero coordinate.
This proof works for any `k` without enumerating all nonzero classes.

The current bicycle generator emits explicit representative lists and integer multiplicities.
Lean checks kernels, class coordinates, per-qubit caps, rank certificates, and the stored upper-bound witnesses.
It does not assume that a cyclic shift preserves the logical class.
The two families for `262-2-15` have `(total, cap)` values `(3930,258)` and `(131,9)` on both sides.
Both satisfy `14*cap < total`, so both prove a lower bound of 15.

This input generator currently supports cyclic two-block codes with `k = 2`.
The generic theorem has no such restriction.
The JSON parser and certificate search remain outside Lean.
The kernel proves statements about the generated matrices and independently accepts every certificate obligation.
