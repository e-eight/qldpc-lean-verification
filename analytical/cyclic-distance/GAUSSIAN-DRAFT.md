# Rotated-square cyclic families — proof fragment pending review

Grade: PROPOSITION pending Lean replay and three independent document-only reviews.
This fragment is intended to be incorporated into the self-contained cyclic-distance
document, whose graph theorem supplies the coding-theoretic part.

**Family theorem.** Let a,h be positive integers, let b be a nonnegative integer,
and suppose gcd(a,b)=1. Set M=a²+b² and m=hM. The binary cyclic square-complex
code with m vertices and steps a,b has 2m physical qubits, both check ranks m−1,
two encoded qubits, and both CSS distances exactly a+b. Every check has weight
at most four and every qubit belongs to at most two checks of each type. Hence
the family has uniformly bounded check weights and qubit degrees, even when
a,b,h vary. At a=r,b=r+1,h=1 with r≥1, the parameters are
[[2(r²+(r+1)²),2,2r+1]].

The construction, rank computation, meaning of the two CSS distances, and
shortest-relation theorem are given in the parent draft. The following argument
proves the arithmetic input without enumeration or numerical certificates.

**Lemma 1 (integral coordinates).** If a,b are coprime integers, M=a²+b²>0,
and au+bv=Mk, there exist integers i,j such that
u=bi+aj and v=−ai+bj.

**Proof.** Choose integers p,q with ap+bq=1. Bézout's identity follows, for
example, by taking the smallest positive member g of {ap+bq:p,q∈Z}; division
with remainder shows g divides both a and b, so g=1 by coprimality.
Put r=bu−av. Direct multiplication using the given equality gives
ar=M(bk−v) and br=M(u−ak). Multiplying the first by p and the second by q
and adding yields r=M[p(bk−v)+q(u−ak)]. Thus set
i=p(bk−v)+q(u−ak), j=k. Then
M(bi+aj)=b(bu−av)+a(au+bv)=Mu and
M(−ai+bj)=−a(bu−av)+b(au+bv)=Mv. Because M>0, cancellation proves both
identities. ∎

**Lemma 2 (norm separation).** Suppose a,b≥0 and i,j are integers not both
zero. Then |bi+aj|+|−ai+bj|≥a+b.

**Proof.** The cases i=0, i≠0 and j=0, and i≠0 and j≠0 are disjoint and
exhaustive. If i=0 then |j|≥1 and the norm is (a+b)|j|≥a+b. If i≠0 and
j=0 then |i|≥1 and the norm is (a+b)|i|≥a+b. In the remaining case put
U=bi+aj, V=−ai+bj and W=|U|+|V|. Since i,j are nonzero integers,
i²+j²≥2. Expansion gives

U²+V² = (a²+b²)(i²+j²) ≥ 2(a²+b²).

Also W²=U²+V²+2|UV|≥U²+V², and
2(a²+b²)−(a+b)²=(a−b)²≥0. Thus W²≥(a+b)². Both W and a+b are
nonnegative, so W≥a+b: if W<a+b, then
(a+b)²−W²=(a+b−W)(a+b+W)>0 unless a+b=W=0, which contradicts the
strict inequality in that case too. ∎

**Lemma 3 (exact cyclic lattice minimum).** Under the family theorem's
hypotheses, the least value of |u|+|v| over nonzero integer pairs satisfying
m divides au+bv is a+b.

**Proof.** If au+bv=mk=hMk, apply Lemma 1 with j=hk. The resulting pair
(i,j) is nonzero because i=j=0 would imply u=v=0. Lemma 2 gives the lower
bound a+b. Conversely the pair (b,−a) is nonzero since a>0, satisfies
ab+b(−a)=0, and has norm a+b. This proves both attainment and minimality.
No bound on h besides positivity was used. ∎

**Proof of the family theorem.** Coprimality of a,b implies
gcd(a,b,m)=1, so the cyclic graph is connected. Apply the parent document's
rank and exact shortest-relation theorem and Lemma 3. There are two labelled
edge types at every vertex, so there are 2m qubits. The vertex row consists
of the two incoming and two outgoing edges, counting repeated appearances
modulo two. The face row consists of four edge appearances. Their weights
are at most four. Each labelled edge has two vertex endpoints and appears
in two translated faces, so each column has weight at most two in each
check matrix. Repeated appearances can cancel and cannot increase these
bounds. At a=r,b=r+1, a common divisor divides their difference 1, and
a+b=2r+1. Substitution gives the displayed specialization. ∎

Attribution: rotated square-lattice codes and the odd-distance specialization
are established constructions, not asserted inventions. Arnault, Gaborit and
Saussay, *“(2,2)-GB Codes: Classification and Comparison with weight-4 Surface
Codes”*, arXiv:2507.21237v1, Section II-E2 and Lemma IV.4, discuss these period
lattices and the odd-distance parameters. Our proof gives a uniform coprime
two-parameter arithmetic interface and positive-cover statement and formalizes
the exact symbolic transfer. No priority claim is made for either statement.
