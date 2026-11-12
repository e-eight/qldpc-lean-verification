# Analytic lattice minima for the existing cyclic bicycle applications

**Grade: PROPOSITION.** The following is a complete paper proof. Its named
acceptance obligations are the final Lean replay and three independent
hostile document-only reviews. It is not yet a final theorem artifact.

## Main theorem

For every row of the following table, let

\[
\Lambda_{m,a}=\{(u,v)\in\mathbb Z^2:m\mid u+av\}.
\]

The least value of $|u|+|v|$ on $\Lambda_{m,a}\setminus\{(0,0)\}$ is
exactly the displayed $D$.

| Existing application | $m$ | $a$ | $D$ |
| --- | ---: | ---: | ---: |
| Bicycle4 | 2 | 1 | 2 |
| Bicycle58 | 29 | 8 | 7 |
| Bicycle82 | 41 | 9 | 9 |
| Bicycle100 | 50 | 9 | 10 |
| Bicycle110 | 55 | 10 | 10 |
| Bicycle122 | 61 | 11 | 11 |
| Bicycle170 | 85 | 13 | 13 |
| Bicycle226 | 113 | 15 | 15 |
| Bicycle262Lattice | 131 | 20 | 15 |
| Bicycle278 | 139 | 30 | 16 |
| Bicycle298 | 149 | 34 | 17 |
| Bicycle346 | 173 | 51 | 18 |
| Bicycle362 | 181 | 19 | 19 |
| Bicycle422 | 211 | 20 | 20 |
| Bicycle454 | 227 | 61 | 21 |
| Bicycle562Family | 281 | 101 | 23 |
| BicycleEven16Family | 8 | 3 | 4 |
| BicycleEvenStep16 | 8 | 2 | 3 |

The first sixteen rows are the existing submitted bicycle applications; the
last two are existing construction regressions. This table specifies the
finite collection of inputs under discussion. The proof treats each through
one general integer-basis criterion. It does not classify all cyclic codes
by enumerating a finite parameter set, and it does not use a lattice-window
search to exclude short vectors.

## 1. Definitions and elementary inequalities

All scalars below are integers unless explicitly declared otherwise.
For an integer $x$, define $|x|=x$ if $x\ge0$ and $|x|=-x$ if $x<0$.
For a pair $z=(x,y)$, define $N(z)=|x|+|y|$ and
$K(z)=\max\{|x|,|y|\}$. For a positive integer $m$, the notation $m\mid z$
means that $z=mk$ for some integer $k$.

The definition of absolute value gives $-|x|\le x\le|x|$ and
$|x|\ge0$. It gives $|-x|=|x|$: for $x\ge0$, $-x\le0$ and both values
are $x$; for $x<0$, $-x>0$ and both values are $-x$. These two cases
are exhaustive. Also $|x|^2=x^2$, by substituting the two branches of
the definition. Consequently $|xy|=|x||y|$: both sides are nonnegative,
their squares equal $x^2y^2$, and two nonnegative integers with equal
squares are equal. Indeed, their squared difference factors as
$(A-B)(A+B)$; if $A+B=0$ both are zero, and if $A+B>0$ cancellation
forces $A=B$.

For integers $x,y$, adding their signed bounds gives
$-(|x|+|y|)\le x-y\le|x|+|y|$. If $x-y\ge0$, the upper bound gives
$|x-y|\le|x|+|y|$; if $x-y<0$, the lower bound gives the same conclusion
by negating. These two cases are exhaustive. It follows that

\[
|xu-yv|\le |x||u|+|y||v|
\le\max\{|x|,|y|\}(|u|+|v|).
\tag{1}
\]

The second inequality follows by multiplying $|x|\le\max\{|x|,|y|\}$
by $|u|\ge0$, multiplying the corresponding inequality for $y$ by
$|v|\ge0$, and adding.

## 2. An integral basis criterion

**Lemma 1.** Let $m>0$, $a\ge0$, and let
$p=(p_1,p_2)$, $q=(q_1,q_2)$ be integer pairs. Suppose integers $r,s$
satisfy

\[
p_1+ap_2=mr,\qquad q_1+aq_2=ms,\qquad rq_2-sp_2=1.
\tag{2}
\]

Then every $(u,v)\in\Lambda_{m,a}$ has unique integer coordinates $i,j$
such that

\[
(u,v)=ip+jq.
\tag{3}
\]

The determinant is $p_1q_2-q_1p_2=m$, and the coordinates satisfy

\[
mi=q_2u-q_1v,\qquad mj=-p_2u+p_1v.
\tag{4}
\]

**Proof.** Subtract $p_2$ times the second identity of (2) from $q_2$
times the first. The terms involving $a$ cancel, giving

\[
p_1q_2-q_1p_2=m(rq_2-sp_2)=m.
\tag{5}
\]

Also $r$ times the second identity minus $s$ times the first gives
$q_1r-p_1s+a(rq_2-sp_2)=0$, hence $q_1r-p_1s=-a$.
For a relation $u+av=mk$, define

\[
i=q_2k-sv,\qquad j=rv-p_2k.
\tag{6}
\]

These are integers. Expanding both reconstructed coordinates gives

\[
\begin{aligned}
p_1i+q_1j
 &= (p_1q_2-q_1p_2)k+(q_1r-p_1s)v
 =mk-av=u,\\
p_2i+q_2j
 &= (p_2q_2-q_2p_2)k+(q_2r-p_2s)v=v.
\end{aligned}
\]

Conversely every pair $ip+jq$ has first coordinate plus $a$ times
second coordinate equal to $m(ri+sj)$ by (2), so it belongs to the
lattice. Applying the two linear expressions in (4) to (3) cancels
all mixed terms and gives respectively $(p_1q_2-q_1p_2)i=mi$ and
$(p_1q_2-q_1p_2)j=mj$. These prove (4). If two coordinate pairs
represent the same vector, (4) makes their multiples by $m$ equal;
cancellation of $m>0$ proves that their coordinates are equal. ∎

## 3. Analytic exclusion of every shorter vector

**Lemma 2.** Assume (2), let $D\ge1$, and suppose

\[
K(p)(D-1)<2m,\qquad K(q)(D-1)<2m.
\tag{7}
\]

If $(u,v)\in\Lambda_{m,a}$ and $N(u,v)<D$, its integral coordinates
satisfy $i,j\in\{-1,0,1\}$.

**Proof.** Because $N(u,v)$ and $D$ are integers, the strict inequality
implies $N(u,v)\le D-1$. Equations (1), (4), and (7) give

\[
\begin{aligned}
m|i|&=|q_2u-q_1v|\le K(q)N(u,v)\le K(q)(D-1)<2m,\\
m|j|&=|p_1v-p_2u|\le K(p)N(u,v)\le K(p)(D-1)<2m.
\end{aligned}
\]

Cancel the positive $m$ to obtain $|i|<2$ and $|j|<2$. These imply
$-1\le i,j\le1$, since they are integers. An integer in this interval
is negative, zero, or positive; in the negative case it must be $-1$,
and in the positive case it must be $1$. This proves the asserted
three possibilities for each coordinate. ∎

**Lemma 3.** Assume (2), (7), and

\[
N(p),\ N(q),\ N(p+q),\ N(p-q)\ \ge D.
\tag{8}
\]

Then every nonzero vector in $\Lambda_{m,a}$ has norm at least $D$.

**Proof.** Suppose a nonzero vector had norm below $D$. Lemma 2 gives
three possibilities for $i$ and three for $j$. Their Cartesian product
is the following exhaustive list; no other pair can occur.

| $i$ | $j$ | Represented vector | Its norm |
| ---: | ---: | --- | --- |
| $0$ | $0$ | $0$ | $0$ |
| $0$ | $1$ | $q$ | $N(q)$ |
| $0$ | $-1$ | $-q$ | $N(q)$ |
| $1$ | $0$ | $p$ | $N(p)$ |
| $1$ | $1$ | $p+q$ | $N(p+q)$ |
| $1$ | $-1$ | $p-q$ | $N(p-q)$ |
| $-1$ | $0$ | $-p$ | $N(p)$ |
| $-1$ | $1$ | $-(p-q)$ | $N(p-q)$ |
| $-1$ | $-1$ | $-(p+q)$ | $N(p+q)$ |

The first case is excluded by nonzeroness. Each of the other eight
cases has norm at least $D$ by (8), using $N(-z)=N(z)$ as proved from
absolute value in Section 1. Each contradicts the assumed strict upper
bound. Thus there is no such vector. ∎

## 4. Complete arithmetic data for the stated inputs

The next tables provide all values required by the three lemmas. They
are small closed integer calculations: the first table supplies the
input vectors; the second explicitly evaluates the relations and the
quotient determinant; the third evaluates the two products in (7) and
the four norms in (8). There is no unevaluated lattice-search premise.

| Application | $p$ | $q$ | $r$ | $s$ |
| --- | --- | --- | ---: | ---: |
| Bicycle4 | (-1, 1) | (-1, -1) | 0 | -1 |
| Bicycle58 | (-3, 4) | (-5, -3) | 1 | -1 |
| Bicycle82 | (-4, 5) | (-5, -4) | 1 | -1 |
| Bicycle100 | (5, 5) | (-4, 6) | 1 | 1 |
| Bicycle110 | (5, 5) | (-5, 6) | 1 | 1 |
| Bicycle122 | (-5, 6) | (-6, -5) | 1 | -1 |
| Bicycle170 | (-6, 7) | (-7, -6) | 1 | -1 |
| Bicycle226 | (-7, 8) | (-8, -7) | 1 | -1 |
| Bicycle262Lattice | (-9, 7) | (-11, -6) | 1 | -1 |
| Bicycle278 | (-8, -9) | (11, -5) | -2 | -1 |
| Bicycle298 | (-8, 9) | (-13, -4) | 2 | -1 |
| Bicycle346 | (-11, 7) | (-9, -10) | 2 | -3 |
| Bicycle362 | (-9, 10) | (-10, -9) | 1 | -1 |
| Bicycle422 | (-9, 11) | (-11, -10) | 1 | -1 |
| Bicycle454 | (-10, -11) | (7, -15) | -3 | -4 |
| Bicycle562Family | (9, -14) | (13, 11) | -5 | 4 |
| BicycleEven16Family | (2, 2) | (-3, 1) | 1 | 0 |
| BicycleEvenStep16 | (-2, 1) | (-2, -3) | 0 | -1 |

For the two relation columns below, the manipulation is respectively
$p_1+ap_2$ and $q_1+aq_2$; the displayed right sides are $mr$ and $ms$.
For the determinant column the manipulation is $rq_2-sp_2$.
Parentheses identify signed inputs explicitly.

| Application | First relation | Second relation | Quotient determinant |
| --- | --- | --- | --- |
| Bicycle4 | $(-1)+1(1)=2(0)=0$ | $(-1)+1(-1)=2(-1)=-2$ | $(0)(-1)-(-1)(1)=1$ |
| Bicycle58 | $(-3)+8(4)=29(1)=29$ | $(-5)+8(-3)=29(-1)=-29$ | $(1)(-3)-(-1)(4)=1$ |
| Bicycle82 | $(-4)+9(5)=41(1)=41$ | $(-5)+9(-4)=41(-1)=-41$ | $(1)(-4)-(-1)(5)=1$ |
| Bicycle100 | $(5)+9(5)=50(1)=50$ | $(-4)+9(6)=50(1)=50$ | $(1)(6)-(1)(5)=1$ |
| Bicycle110 | $(5)+10(5)=55(1)=55$ | $(-5)+10(6)=55(1)=55$ | $(1)(6)-(1)(5)=1$ |
| Bicycle122 | $(-5)+11(6)=61(1)=61$ | $(-6)+11(-5)=61(-1)=-61$ | $(1)(-5)-(-1)(6)=1$ |
| Bicycle170 | $(-6)+13(7)=85(1)=85$ | $(-7)+13(-6)=85(-1)=-85$ | $(1)(-6)-(-1)(7)=1$ |
| Bicycle226 | $(-7)+15(8)=113(1)=113$ | $(-8)+15(-7)=113(-1)=-113$ | $(1)(-7)-(-1)(8)=1$ |
| Bicycle262Lattice | $(-9)+20(7)=131(1)=131$ | $(-11)+20(-6)=131(-1)=-131$ | $(1)(-6)-(-1)(7)=1$ |
| Bicycle278 | $(-8)+30(-9)=139(-2)=-278$ | $(11)+30(-5)=139(-1)=-139$ | $(-2)(-5)-(-1)(-9)=1$ |
| Bicycle298 | $(-8)+34(9)=149(2)=298$ | $(-13)+34(-4)=149(-1)=-149$ | $(2)(-4)-(-1)(9)=1$ |
| Bicycle346 | $(-11)+51(7)=173(2)=346$ | $(-9)+51(-10)=173(-3)=-519$ | $(2)(-10)-(-3)(7)=1$ |
| Bicycle362 | $(-9)+19(10)=181(1)=181$ | $(-10)+19(-9)=181(-1)=-181$ | $(1)(-9)-(-1)(10)=1$ |
| Bicycle422 | $(-9)+20(11)=211(1)=211$ | $(-11)+20(-10)=211(-1)=-211$ | $(1)(-10)-(-1)(11)=1$ |
| Bicycle454 | $(-10)+61(-11)=227(-3)=-681$ | $(7)+61(-15)=227(-4)=-908$ | $(-3)(-15)-(-4)(-11)=1$ |
| Bicycle562Family | $(9)+101(-14)=281(-5)=-1405$ | $(13)+101(11)=281(4)=1124$ | $(-5)(11)-(4)(-14)=1$ |
| BicycleEven16Family | $(2)+3(2)=8(1)=8$ | $(-3)+3(1)=8(0)=0$ | $(1)(1)-(0)(2)=1$ |
| BicycleEvenStep16 | $(-2)+2(1)=8(0)=0$ | $(-2)+2(-3)=8(-1)=-8$ | $(0)(-3)-(-1)(1)=1$ |

For each norm quadruple, the four operations are
$|p_1|+|p_2|$, $|q_1|+|q_2|$,
$|p_1+q_1|+|p_2+q_2|$, and $|p_1-q_1|+|p_2-q_2|$.
The displayed products multiply the largest absolute coordinate by $D-1$.
Every product is strictly smaller than the displayed $2m$, and every norm
is at least the displayed $D$.

| Application | $D$ | $K(p)(D-1)$ | $K(q)(D-1)$ | $2m$ | $(N(p),N(q),N(p+q),N(p-q))$ |
| --- | ---: | --- | --- | ---: | --- |
| Bicycle4 | 2 | $1\cdot1=1$ | $1\cdot1=1$ | 4 | (2, 2, 2, 2) |
| Bicycle58 | 7 | $4\cdot6=24$ | $5\cdot6=30$ | 58 | (7, 8, 9, 9) |
| Bicycle82 | 9 | $5\cdot8=40$ | $5\cdot8=40$ | 82 | (9, 9, 10, 10) |
| Bicycle100 | 10 | $5\cdot9=45$ | $6\cdot9=54$ | 100 | (10, 10, 12, 10) |
| Bicycle110 | 10 | $5\cdot9=45$ | $6\cdot9=54$ | 110 | (10, 11, 11, 11) |
| Bicycle122 | 11 | $6\cdot10=60$ | $6\cdot10=60$ | 122 | (11, 11, 12, 12) |
| Bicycle170 | 13 | $7\cdot12=84$ | $7\cdot12=84$ | 170 | (13, 13, 14, 14) |
| Bicycle226 | 15 | $8\cdot14=112$ | $8\cdot14=112$ | 226 | (15, 15, 16, 16) |
| Bicycle262Lattice | 15 | $9\cdot14=126$ | $11\cdot14=154$ | 262 | (16, 17, 21, 15) |
| Bicycle278 | 16 | $9\cdot15=135$ | $11\cdot15=165$ | 278 | (17, 16, 17, 23) |
| Bicycle298 | 17 | $9\cdot16=144$ | $13\cdot16=208$ | 298 | (17, 17, 26, 18) |
| Bicycle346 | 18 | $11\cdot17=187$ | $10\cdot17=170$ | 346 | (18, 19, 23, 19) |
| Bicycle362 | 19 | $10\cdot18=180$ | $10\cdot18=180$ | 362 | (19, 19, 20, 20) |
| Bicycle422 | 20 | $11\cdot19=209$ | $11\cdot19=209$ | 422 | (20, 21, 21, 23) |
| Bicycle454 | 21 | $11\cdot20=220$ | $15\cdot20=300$ | 454 | (21, 22, 29, 21) |
| Bicycle562Family | 23 | $14\cdot22=308$ | $13\cdot22=286$ | 562 | (23, 24, 25, 29) |
| BicycleEven16Family | 4 | $2\cdot3=6$ | $3\cdot3=9$ | 16 | (4, 4, 4, 6) |
| BicycleEvenStep16 | 3 | $2\cdot2=4$ | $3\cdot2=6$ | 16 | (3, 5, 6, 4) |

These entries verify every hypothesis of Lemma 3 for every input row.
To be explicit about the final comparison, every $m$ is positive and
all displayed $D$ are positive. In each of the eighteen rows, both
product entries are less than its $2m$ entry; comparison of the four
norm entries with its $D$ entry verifies all four inequalities in (8).
Together with the three exact equalities in the preceding table, this
proves the lower bound $D$ for each stated input.

## 5. Attainment and completion of the theorem

A member of the following list attains each bound. The selected vector
is either $p$, $q$, or $p-q$, as indicated. Lemma 1 proves these are
lattice vectors; the table also gives the direct divisibility calculation.
The first or second coordinate is nonzero in every displayed pair, so
these are nonzero lattice vectors.

| Application | Selected vector $(u,v)$ | Choice | $u+av$ | $|u|+|v|=D$ |
| --- | --- | --- | --- | --- |
| Bicycle4 | (-1, 1) | $p$ | $(-1)+1(1)=0=2(0)$ | $1+1=2$ |
| Bicycle58 | (-3, 4) | $p$ | $(-3)+8(4)=29=29(1)$ | $3+4=7$ |
| Bicycle82 | (-4, 5) | $p$ | $(-4)+9(5)=41=41(1)$ | $4+5=9$ |
| Bicycle100 | (5, 5) | $p$ | $(5)+9(5)=50=50(1)$ | $5+5=10$ |
| Bicycle110 | (5, 5) | $p$ | $(5)+10(5)=55=55(1)$ | $5+5=10$ |
| Bicycle122 | (-5, 6) | $p$ | $(-5)+11(6)=61=61(1)$ | $5+6=11$ |
| Bicycle170 | (-6, 7) | $p$ | $(-6)+13(7)=85=85(1)$ | $6+7=13$ |
| Bicycle226 | (-7, 8) | $p$ | $(-7)+15(8)=113=113(1)$ | $7+8=15$ |
| Bicycle262Lattice | (2, 13) | $p-q$ | $(2)+20(13)=262=131(2)$ | $2+13=15$ |
| Bicycle278 | (11, -5) | $q$ | $(11)+30(-5)=-139=139(-1)$ | $11+5=16$ |
| Bicycle298 | (-8, 9) | $p$ | $(-8)+34(9)=298=149(2)$ | $8+9=17$ |
| Bicycle346 | (-11, 7) | $p$ | $(-11)+51(7)=346=173(2)$ | $11+7=18$ |
| Bicycle362 | (-9, 10) | $p$ | $(-9)+19(10)=181=181(1)$ | $9+10=19$ |
| Bicycle422 | (-9, 11) | $p$ | $(-9)+20(11)=211=211(1)$ | $9+11=20$ |
| Bicycle454 | (-10, -11) | $p$ | $(-10)+61(-11)=-681=227(-3)$ | $10+11=21$ |
| Bicycle562Family | (9, -14) | $p$ | $(9)+101(-14)=-1405=281(-5)$ | $9+14=23$ |
| BicycleEven16Family | (2, 2) | $p$ | $(2)+3(2)=8=8(1)$ | $2+2=4$ |
| BicycleEvenStep16 | (-2, 1) | $p$ | $(-2)+2(1)=0=8(0)$ | $2+1=3$ |

Section 4 proves that no nonzero relation has smaller norm. This table
supplies a relation of exactly that norm. Therefore the set of nonzero
relation norms is nonempty and its minimum is exactly $D$ in every
row, completing the main theorem. ∎

## 6. Formalization and reproducibility

`lean/QldpcVerification/Lattice/BasisSeparation.lean` formalizes the
integer-basis identities, the inverse-coordinate estimate, and all nine
derived coefficient cases. Its `BasisData.bound` theorem accepts the
normalized congruence in `ZMod m`, converts it to divisibility, and applies
the proved separation argument. The compatibility theorem named
`finite_exclusion` in each instance module now follows from this symbolic
bound. It is not established by evaluation of a grid.

The eighteen `Lattice/Bicycle*Arithmetic.lean` modules contain the displayed
basis data. Their `bound` theorems instantiate the general criterion, and
`shortest_relation` supplies the attaining integer pair. `norm_num` checks
only the closed integer calculations printed in the tables above. The proof
of the universal bound is the symbolic three-lemma argument, not a computed
list of short vectors.

`scripts/bicycle_lattice_arithmetic.py` is included in the project. It finds
candidate bases using exact integer swaps and shears and checks exactly the
printed identities and inequalities before emitting Lean source. Its input
is the table of $(m,a,D)$ above, supplied by the existing instance generator.
The initial lattice basis is $(m,0),(-a,1)$; swapping basis vectors and
replacing one by itself minus an integer multiple of the other preserve
their integer span. The implementation uses exact integer arithmetic,
not floating point. The proof does not assume that basis discovery succeeds
on arbitrary inputs: any emitted basis must satisfy the explicit conditions
proved sufficient here. The basis choice has no mathematical authority of
its own. A reader can verify every instance directly from the displayed
values without executing any script.

The focused regression tests check an example whose shortest listed vector
is the basis difference, the exact half-integer reduction boundary, a very
large congruent step, a zero step, rejection of false lower bounds, and
rejection of a claimed distance lacking attainment. They are engineering
checks; none is a premise of the main theorem.

This argument is elementary integer linear algebra and norm estimation.
No claim of mathematical priority is made. Every fact used by the arithmetic
proof has been established explicitly in this document.
