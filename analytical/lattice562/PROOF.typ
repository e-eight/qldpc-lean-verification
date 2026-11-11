#set page(paper: "a4", margin: 22mm)
#set text(size: 11pt)
#set par(justify: true)
#set heading(numbering: "1.")
= Exact separation of an integer period lattice

*Grade: THEOREM. Independently refereed and formalized in Lean.*

*Main statement.* Let $u,v$ be integers, not both zero, such that $281$ divides
$7u+145v$. Then $abs(u)+abs(v) >= 23$. Equality is attained at $(u,v)=(9,-14)$.
The assertion concerns only this explicitly defined integer lattice.

= Definitions

For an integer $t$, $abs(t)=t$ when $t>=0$, and $abs(t)=-t$ when $t<0$.
For integers $m,t$, the notation $m mid t$ means that $t=m k$ for an integer $k$.
The lattice in the statement is the set
$ Lambda = {(u,v) in ZZ^2 : 281 mid (7u+145v)}. $
The length used here is the sum $abs(u)+abs(v)$, not Euclidean length.
A basis means that every lattice vector has a unique expression as an integer
linear combination of the displayed vectors.

= An explicit basis

*Lemma 1.* The vectors $p=(9,-14)$ and $q=(13,11)$ are a basis of $Lambda$.
For $(u,v) in Lambda$, writing $7u+145v=281k$, its coefficients are
$ a=122k-3u-63v, quad b=2k-v, $
and satisfy
$ 281a=11u-13v, quad 281b=14u+9v, $
$ u=9a+13b, quad v=-14a+11b. $

*Proof.* First,
$7 dot 9+145 dot (-14)=63-2030=-1967=-7 dot 281$ and
$7 dot 13+145 dot 11=91+1595=1686=6 dot 281$.
Thus integer combinations of $p,q$ belong to $Lambda$.
Conversely, choose the integer $k$ in the definition of divisibility and use the
formulas for $a,b$. Substitution gives
$ 281a &=122(7u+145v)-843u-17703v \
       &=(854-843)u+(17690-17703)v=11u-13v, $
$ 281b=2(7u+145v)-281v=14u+9v. $
Consequently
$ 281(9a+13b)=9(11u-13v)+13(14u+9v)=281u, $
$ 281(-14a+11b)=-14(11u-13v)+11(14u+9v)=281v. $
Cancellation of the nonzero integer $281$ proves the reconstruction formulas.
For any other representation $u=9a'+13b'$ and $v=-14a'+11b'$, expansion gives
$11u-13v=(99+182)a'+(143-143)b'=281a'$ and
$14u+9v=(126-126)a'+(182+99)b'=281b'$.
Comparing these identities with those for $a,b$ and cancelling $281$ gives
$a'=a$ and $b'=b$. This proves uniqueness. $square$

= Small length forces small basis coefficients

*Lemma 2.* If $(u,v) in Lambda$ and $abs(u)+abs(v)<=22$, its coefficients in
Lemma 1 belong to $\{-1,0,1\}$.

*Proof.* The definition of absolute value gives $-abs(t)<=t<=abs(t)$.
Adding these inequalities for two integers $s,t$ gives
$-abs(s)-abs(t)<=s+t<=abs(s)+abs(t)$, hence
$abs(s+t)<=abs(s)+abs(t)$: when $s+t>=0$ use the upper bound, and when
$s+t<0$ negate the lower bound. These two cases exhaust the integers.
For a nonnegative integer $c$, $abs(c t)=c abs(t)$, using the cases $t>=0$
and $t<0$ in the definition. Also $abs(-t)=abs(t)$ by those same two cases.
Therefore Lemma 1 implies
$281 abs(a)=abs(11u-13v)<=11 abs(u)+13 abs(v)
  <=13(abs(u)+abs(v))<=286<562=2 dot 281,$
$281 abs(b)=abs(14u+9v)<=14 abs(u)+9 abs(v)
  <=14(abs(u)+abs(v))<=308<562=2 dot 281.$
Thus $abs(a)<2$ and $abs(b)<2$. An integer with absolute value less than two
is at least $-1$ and at most $1$, and the only integers in that interval are
$-1,0,1$. This proves the list of possibilities without a search. $square$

= Proof of the main statement

Suppose its lower bound fails. The length is an integer, so it is at most $22$.
Lemmas 1 and 2 apply. The following table lists *all* possibilities: each of $a$
and $b$ belongs to the three-element set proved in Lemma 2, and for each
value of $a$ all three values of $b$ appear. Its third column substitutes into
$(u,v)=(9a+13b,-14a+11b)$; its last column adds the two absolute values.

#table(
  columns: 4, align: center, inset: 6pt,
  [$a$], [$b$], [$(u,v)$], [$abs(u)+abs(v)$],
  [$-1$], [$-1$], [$(-22,3)$], [$25$],
  [$-1$], [$0$], [$(-9,14)$], [$23$],
  [$-1$], [$1$], [$(4,25)$], [$29$],
  [$0$], [$-1$], [$(-13,-11)$], [$24$],
  [$0$], [$0$], [$(0,0)$], [$0$],
  [$0$], [$1$], [$(13,11)$], [$24$],
  [$1$], [$-1$], [$(-4,-25)$], [$29$],
  [$1$], [$0$], [$(9,-14)$], [$23$],
  [$1$], [$1$], [$(22,-3)$], [$25$],
)

Every nonzero row has length greater than $22$. The sole remaining row is the
zero vector, excluded by hypothesis. This proves the lower bound. Finally
$9+14=23$ and $7 dot 9+145 dot(-14)=-7 dot 281$, so the stated nonzero vector
attains the bound. $square$

All displayed arithmetic consists of multiplication, addition, and cancellation
of the stated integers. No generated case list, numerical certificate, or
exhaustive lattice search is an input to this proof.
