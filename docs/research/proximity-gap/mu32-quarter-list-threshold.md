# Four list thresholds on the 32nd roots of unity

For every field of characteristic zero or characteristic above $2^{118}$ containing $\mu_{32}$, the first closed Hamming ball containing four distinct degree-below-eight Reed–Solomon words on $\mu_{32}$ occurs at **16 errors**. This holds on every nonzero coset, in every coordinate ordering, and at every positive finite interleaving width. The proof uses a finite exhaustive calculation over the integers and $\mathbb F_{65537}$.

Together with the three other rates, this determines the entire four-rate **list** table on the prime $p=(3\cdot 2^{48}+69)2^{80}+1$, for which $\lfloor p/2^{128}\rfloor=3$.

| Rate | Dimension | Last good integer radius | First failing radius | Operational supremum |
|---|---:|---:|---:|---:|
| $1/2$ | 16 | 9 | 10 | $5/16$ |
| $1/4$ | 8 | 15 | 16 | $1/2$ |
| $1/8$ | 4 | 19 | 20 | $5/8$ |
| $1/16$ | 2 | 22 | 23 | $23/32$ |

Each supremum is excluded. The half-rate theorem uses $p>2^{128}$. The last two rows hold in every field admitting the domain. [Half-rate proof](mu32-list-threshold-large-characteristic.md) · [Cubic Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/Mu32CubicList.lean) · [Linear proof](PROGRESS.md#2026-11-21--exact-list-budget-three-boundary-for-dimension-two)

## Three finite fiber facts

For an exponent set $A\subseteq\mathbb Z/32$, write $L_A(X)=\prod_{a\in A}(X-z^a)$ at a primitive root $z$. Suppose $A,B,U$ are pairwise disjoint, $|A|=|B|=m$, and $L_A/L_B$ is constant on $U$.

1. The case $m=|U|=5$ is impossible.
2. For $m=6$ and $|U|\ge5$, both $A$ and $B$ are closed under $a\mapsto a+16$.
3. For $m=7$, even $|U|=6$ is impossible.

First lift the equalities to $\mathbb Q(\zeta_{32})$. The graph joining nonantipodal pairs of $U$ is connected when $|U|\ge3$. For each such edge the integer verification of the cyclotomic norm bound gives largest upper exponents $101776/1024,111426/1024,120222/1024$ for $m=5,6,7$, respectively, on the odd part of the norm of the cross-multiplied difference. All three are below 118. A difference vanishing in characteristic $p>2^{118}$ must therefore already vanish in the cyclotomic field. In characteristic zero the identities hold there directly. [Norm inequality and exact rounding](mu32-list-threshold-large-characteristic.md#lifting-a-constant-ratio-of-vanishers) · [Norm verifier](../../../scripts/probes/probe_mu32_ratio_norm.py)

Choose five of the test exponents. Translation and odd multiplication act on them by rotating the roots and applying Galois automorphisms. Among normalized five-sets containing exponent zero there are 454 minimum representatives for this action. For each representative $T$, enumerate every $m$-subset of its 27-element complement. Reduce the vanisher values at $T$ modulo 65537 with $z=3^{2048}$. Every value is nonzero. Normalize each five-vector by its first coordinate and sort by the other four coordinates. Equal vectors identify all possible pairs. Reject intersecting supports. Recheck the identities at $z^j$ for $j=1,3,\ldots,15$. For degree seven, require at least six test-site matches in each specialization. Every characteristic-zero solution passes all these necessary tests. The survivor counts over the 454 representatives are respectively **0, 8, 0**. All eight degree-six pairs have both supports closed under the antipode. [Fiber verifier](../../../scripts/probes/probe_mu32_quarter_fibers.cpp)

## Four polynomials at seventeen agreements

Suppose four distinct polynomials $P_0,\ldots,P_3$ of degree at most seven each agree with a received word on at least 17 sites. Write $r_{ij}$ for the number of sites on which $P_i=P_j$, $d_{ij}=7-r_{ij}$, $d=\sum_{i<j}d_{ij}$ and $d_i=\sum_{j\ne i}d_{ij}$. Call an edge full when $r_{ij}=7$. For the partitions of the four values at a site, let $Z,D,T,Q$ count respectively the all-distinct, two-disjoint-pairs, triple-and-singleton, and quadruple cases. Write $T_i$ for the number of triple-only sites omitting $i$. The other sites have exactly one pair.

Counting pair coincidences gives $D+2T+5Q-Z=10-d$. The sum of the largest block sizes is $64+T+2Q-Z\ge68$. Hence
$$d+D+Q+Z\le2.$$
Whenever equality holds here, the two identities give a total of exactly 68 for the sum of largest blocks. Every chosen center value must then be in a largest block, and each word has exactly 17 agreements.

For a triangle of heads, remove its common sites from all three edge root sets. The remaining three sets are pairwise disjoint. Each full edge difference equals a scalar times the common vanisher times the vanisher of its remaining set. If two edges are full, the ratio of their remaining vanishers is constant on the remaining sites of the third edge. This follows by subtraction of the two differences. In particular a full triangle omitting head $i$ cannot have $Q+T_i=0$ or $2$, by the degree-seven and degree-five exclusions. For $Q+T_i=1$ each of its three edges becomes antipodally closed after deleting its common site, by the degree-six test.

**Total deficiency two.** Here $D=Q=Z=0$, $T=4$. The edge coincidences incident to head $i$ count its agreements once at pair sites and twice at triples containing it. Subtract the excess at those triples to get $17=21-d_i-(4-T_i)$, hence $T_i=d_i$. If all deficiencies share one vertex, its complement is a full triangle with $T_i=2$, impossible. Otherwise two opposite edges have deficiency one each. Each triangle has its own single triple site. Fix one deficient edge with six-root set $U$. At each of its two adjoining triangles let $s$ be the common site. The other two edges are full, and after deleting $s$ their six-sets have constant vanisher ratio on the five sites $U\setminus\{s\}$. Both six-sets are antipodal, so the deficient difference divided by $X-s$ is even. Its five roots in $U\setminus\{s\}$ extend by negation to at least six roots on the domain. They all belong to $U$, so the sixth includes $s$. The deficient difference has a double root at $s$. The two triangle sites are distinct and yield two double roots among six different roots of a nonzero polynomial of degree at most seven, a contradiction.

**Total deficiency one.** Label the deficient edge $12$, so $d_1=d_2=1$ and the triangles omitting 1 or 2 are full. The two count identities restrict $(Q,T,D,Z)$ to $(1,2,0,0),(0,4,1,0),(0,5,0,1)$. Each case reaches exactly 68 agreements.

* In the first case, counting the agreements of head $i$ from its incident edges gives $17=21-d_i-(2-T_i)-2$. Thus $T_1=T_2=1$, giving full triangles with two common sites.
* In the second case let $o_i$ indicate membership in the ignored pair at the double-pair site. The count gives $T_i=d_i+o_i$. Values of 2 are impossible for $i=1,2$, so both full triangles have different singleton triple marks. Deleting either mark from their common seven-element edge would make it antipodally closed. Two such deletions are impossible, since two antipode-closed sets have antipode-closed differences, and a singleton cannot be antipode-closed.
* In the last case let $\varepsilon_i$ indicate the single head chosen at the all-distinct site. Then $T_i=1+d_i-\varepsilon_i$. At least one of $T_1,T_2$ equals 2.

**Zero deficiency.** All four triangles are full. If $Q=2$ then $D=Z=T=0$, giving two common sites in each triangle. If $Q=0$, every $T_i$ is positive and different from 2. Also $T\le6$ by the count identities. At least three $T_i$ must therefore equal 1. Two of their full triangles make two different deletions from their common edge antipodally closed.

In the remaining case $Q=1$, write $s$ for the quadruple site. The counts give $2\le T\le3$. Each $T_i$ avoids 1, so all proper triple sites omit the same head. Each of the other three triangles has $s$ as its only common site. They cover all six edges. Consequently each edge difference divided by $X-s$ is a scalar times an even polynomial with six distinct domain roots outside $s$. It cannot vanish at $-s$, as evenness would supply the seventh root $s$. The four heads are therefore all distinct at $-s$. Now $Z\ge1$ forces $T=3$. On sites outside $\{s,-s\}$ each edge's equality indicator is preserved by negation, so proper triple sites occur in antipodal pairs. This contradicts $T=3$.

## Four words at sixteen errors

Use $H=\langle z\rangle$, $u=z^2$. Let $A,B,C$ be the cubic vanishers at the powers of $u$ with exponent sets $(0,1,2),(0,3,11),(0,10,13)$. Scale $B$ to equal $A$ at $u^4$ and $C$ to equal $A$ at $u^8$. Take zero and these three scaled cubics, compose with $X^2$, and multiply by $X-z^{17}$. The four words have degree at most seven. The scale denominators are products of differences of distinct sites. Distinct cubic root sets distinguish the words after every specialization, since a nonzero degree-seven polynomial has at most seven roots.

For exponents $j$ reduced modulo 16, choose the following agreeing heads at $z^j$, with all four chosen at the additional site $j=17$.

| $j\bmod16$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| heads | 0123 | 01 | 01 | 02 | 12 | 12 | free | free | 13 | 23 | 03 | 02 | 23 | 03 | 13 | free |

All stated equalities hold in $\mathbb Z[z]/(z^{16}+1)$ after clearing denominators. This secures $14,14,15,15$ agreements. Assign the six free sites to the four heads in counts $2,2,1,1$. This lower construction works over every field admitting the domain. [Integral witness verifier](../../../scripts/probes/probe_mu32_quarter_witness.py)

A nonzero rescaling of $X$ and permutation of sites transport both bounds to every smooth coset. For four distinct interleaved heads, choose a scalar linear combination of rows distinguishing every pair. At most six proper hyperplanes of coefficients are excluded, and the field has more than six elements. All existing agreements survive. Embedding the scalar example into one row gives the matching interleaved construction.
