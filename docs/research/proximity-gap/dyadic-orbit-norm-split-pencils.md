# An odd split pencil occupies at most six full residue classes modulo 16

Let $n=16q$ be dyadic, $256\le n\le 2^{30}$, and use either named prime field. Suppose a degree-$4q-1$ rational function has three complete simple fibers on $\mu_n$. Among the sixteen residue classes of site exponents modulo 16, **at most six can be contained in the three individual fibers**. Each class has $q$ sites. At production length this is 67,108,864 sites per class. The result allows every placement of the remaining roots.

For the punctured half-rate four-list problem, let $b_i$ count the complete exponent classes contained in private class $U_i$. The three overlap shapes all give $b_0+b_1+b_2\le6$ and $b_0+b_1+b_3\le6$, since each private class is contained in its corresponding pencil fiber. In the six-double shape every private triple admits such a pencil, so $\sum b_i\le8$. In the other two shapes $\sum b_i\le9$, using $b_i\le3$. Configurations with fewer complete classes still require analysis. [Two pencils for the punctured endpoint](half-four-fiber-parity.md)

## Norms of evaluations on complete cosets

Let $G=\mu_{Nq}$, $H=\mu_q$, and let $w=1_P-1_D$ be the signed indicator of two disjoint site sets. The function $R=L_P/L_D$ is the ratio of their monic locators. Write
$$
 s(j)=\sum_{z^q=\zeta_N^j}w(z),\qquad
 R_s(Y)=\prod_{j:s(j)\ne0}(Y-\zeta_N^j)^{s(j)}.
$$
The product of $R$ on the complete coset $xH$ is a fixed sign times $R_s(x^q)$, at every coset avoiding both supports. Indeed $\prod_{h\in H}(xh-z)=(-1)^{q-1}(x^q-z^q)$. Hence equal ratio values on two complete cosets give equal weighted ratio values on the quotient. This uses all the comparisons on both cosets and allows arbitrary subsets of every other coset.

At both named primes every equality of these quotient ratios lifts to the complex roots with the same exponents in the following ranges.

| Quotient $N$ | Arbitrary integer weights | Largest covered input length $Nq$ |
|---:|---:|---:|
| 16 | $\lvert s(j)\rvert\le q\le2^{26}$ | $2^{30}$ |
| 32 | $\lvert s(j)\rvert\le q\le512$ | 16,384 |

To see this, choose a primitive root $z$ of order $N$ and primitive units $1-z^r$ for odd $1\le r<N/2$. The quotient of the values at $y,x$ is an $N$-th root of unity times the product of these units to powers
$$
 e_r=\sum_{a=0}^{\log_2 N-1}\sum_{\sigma=\pm1}
       (s(y+\sigma 2^a r)-s(x+\sigma 2^a r)).
$$
The factorization is integral and uses $1-Z^2=(1-Z)(1+Z)$. The antipodal index is counted twice at the last level. The bound is $4q\log_2 N$. If the ratio values agree, the product of the units raised to $Ne_r$ equals one. [Unit factorization and source logarithms](mu64-unit-lattice-transfer.md)

The exact verifier derives the small-order unit logarithms from the existing order-64 projection and checks each logarithm by exponentiation. It verifies an integer basis $B$ of the projected kernel by row membership and full determinant, using exact rational Gram–Schmidt. If $e=cB$ lies in the exponent cube of radius $D$, its coordinates satisfy $|c_j|\le\lfloor D\sum_i|(B^{-1})_{ij}|\rfloor$. The verifier enumerates products in each of two complementary halves of that rectangle in the original prime field. It checks injectivity of the first half and finds exactly one matching pair, the two zero vectors. Thus $e=0$; specialization preserves the order of the remaining root of unity and hence the original equality. Every primitive root is obtained by an odd change of generator, which permutes these units up to torsion.

| Field | Quotient | Exponent bound | Numbers of tested half-products | Matches |
|---|---:|---:|---:|---:|
| First | 16 | 1,073,741,824 | 44,585 + 82,665 | 1 |
| Second | 16 | 1,073,741,824 | 594,825 + 765,697 | 1 |
| First | 32 | 10,240 | 67,507 + 70,875 | 1 |
| Second | 32 | 10,240 | 598,125 + 639,711 | 1 |

The resulting *integer* equations $e_r=0$ will be used directly. They also imply that if three complete same-parity classes are centers, then $s(j)=s(j+N/2)$ on the opposite parity. The characteristic-zero three-center argument for signed weights uses addition of the weights and still applies to integer values. [Exact weighted verifier](../../../scripts/probes/probe_dyadic_orbit_norm.py) · [Three-center argument](quarter-dyadic-parity.md#three-equal-ratios-in-one-parity-class)

## Rotation forces nearly uniform counts in the nine remaining classes

Label the three fibers $A,B,C$. Their common size is $m=4q-1$. Under every nonidentity element of $H$, at least $m+2=4q+1$ sites leave their own fiber. Indeed the cross product of a pencil and its rotation has degree at most $2m-1$ and also vanishes at zero. Invariance would preserve the odd-size zero fiber under a rotation of even order. [Rotation bound](half-four-fiber-parity.md#rotation-distance-over-the-production-field)

Choose seven full classes. Each fiber contains at most three. Up to permutation, the numbers $f_i$ chosen in the three fibers are $(3,3,1)$ or $(3,2,2)$. For the remaining nine indices $J$, let $t_{ij}$ count sites of fiber $i$ in block $j$, with total $M_i=(4-f_i)q-1$. For one block with $t$ occupied sites, summing its displacement over $H$ counts all $t(q-t)$ ordered pairs from an occupied to an unoccupied site. Consequently
$$
 (q-1)(4q+1)\le\sum_{i,j\in J}t_{ij}(q-t_{ij}).
$$
Here and below $i$ runs over the three fibers. Subtracting each row mean gives
$$
 V:=\sum_{i,j\in J}(t_{ij}-M_i/9)^2
 \le q^2+1-\tfrac19\sum_i M_i^2 .
$$
For $(3,3,1)$ the right side is $(-2q^2+10q+6)/9<0$ for $q\ge8$. For $(3,2,2)$ it gives $9V\le10q+6$.

## A weighted ratio test forces $V\ge 8q^2/99$

Let $T,P,D$ be the three sets of **selected block indices** in a permutation of the roles center, numerator, denominator. The ratio of the two monic fiber locators for $P,D$ is constant on the third fiber. Indeed three fibers of a pencil give three pairwise coprime, linearly dependent locators. For each pair $x,y\in T$ and each primitive unit $r$, let $h_j$ be the coefficients of $s(j)$ in $e_r$ above. The true signed population satisfies $\sum h_j s(j)=0$.

In the reference population each row is constant on $J$, with its actual mean. Its signed difference is $q w_j/9$, where $w_j=9$ on $P$, $-9$ on $D$, zero on $T$, and $|D|-|P|$ on $J$. Put
$$
 O=\sum_j h_jw_j,\qquad
 K=9\sum_{j\in J}h_j^2-\left(\sum_{j\in J}h_j\right)^2 .
$$
Subtract the mean of $h$ on $J$, since the two deviation rows each sum to zero. Cauchy–Schwarz bounds the squared mismatch by
$$
 (qO/9)^2\le (K/9)\,2V .
$$
Thus a comparison with $O\ne0$ and $K=0$ is impossible. Otherwise it yields $V/q^2\ge O^2/(18K)$ when $K>0$.

The exhaustive calculation runs over the 560 choices of $T$ of size three and an unordered pair of disjoint two-element subsets of the remaining 13 sites. It considers every pair of centers in every role and all four primitive units. Among **1,201,200 placements**, the minimum of the largest lower bound available to a placement is exactly $8/99$. A quicker mode first identifies size-three center sets up to translation and multiplication by odd integers, leaving nine representatives and 19,305 layouts. Translation permutes the site columns; odd multiplication also permutes the primitive-unit indices up to sign. Both modes compare integers by cross multiplication. Reproduce the full run with `python3 scripts/probes/probe_split_pencil_six_blocks.py --all-layouts`. [Exact placement verifier](../../../scripts/probes/probe_split_pencil_six_blocks.py)

Finally $8q^2/99>(10q+6)/9$ for $q\ge16$. Hence neither distribution of seven complete classes occurs. The Lean module verifies the variance identity, the application of Cauchy–Schwarz, and both numerical contradictions. The quotient factorization, application of the polynomial rotation theorem, and two finite certificates are the written and executable parts of this proof. [Lean variance inequalities](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilBlockVariance.lean)

## Two fibers cannot each contain three whole classes

For either named field, even six full classes are impossible when three belong to each of two fibers. This holds from $n=128$ through $2^{30}$. To prove it, select three classes from each of $A,B$. Write $t_{ij}$ for the populations on the ten unassigned blocks. Their row totals are $q-1,q-1,4q-1$. The rotation count above gives $\sum t_{ij}^2\le2q^2+1$. Put $s_{ij}=(t_{ij}+1/10)/q$, giving row sums $1,1,4$. Then
$$
 q^2\sum s_{ij}^2 \le 2q^2+6q/5+7/10 .
$$
The same offset in every row cancels in the signed population equations. At each pair of centers in $A$, every order-16 primitive-unit row $h$ therefore imposes
$$
 \sum_{j\text{ unassigned}} h_j(s_{Bj}-s_{Cj})=-\sum_{j\in B}h_j.
$$
The roles of $A,B$ may be exchanged. Here the letters on the right denote the three selected complete class indices.

There are 2,574 placements after normalizing the first triple by affine exponent changes. Over the rationals, 233 linear systems are inconsistent. In the other 2,341 the minimum possible $\sum s_{ij}^2$ is always at least $11/5$, with equality for first triple $\{0,2,8\}$ and second triple $\{4,10,12\}$. This contradicts the rotation inequality for $q\ge8$.

The verifier orthogonalizes the integer equations and their right-hand sides simultaneously. A resulting $0=c$ with $c\ne0$ detects inconsistency. The mutually orthogonal equations $a_i\cdot s=c_i$ have least squared solution norm $\sum_i c_i^2/(a_i\cdot a_i)$, by projection onto their row span. Clearing integer factors in elimination preserves the equations. Both forward and reverse elimination give the stated counts and minimum. [Exact linear systems](../../../scripts/probes/probe_split_pencil_dense_blocks.py)

## Five complete classes force millions of deficits in a pair of other blocks

Suppose $A$ contains three complete classes and $B$ contains two. Choose **any** two other class indices as targets for $C$, and let $e$ be the total number of sites there outside $C$. At length $2^{30}$, **$e\ge4,979,231$**. Thus the conclusion restricts the placement of $C$ even if it contains no whole block.

Use the seven-class reference population $u$ from the preceding variance argument. It consists of three full $A$ blocks, two full $B$ blocks and two target $C$ blocks. On the nine remaining blocks it assigns each row its mean for that reference, namely $(q-1)/9,(2q-1)/9,(2q-1)/9$. Let $W=\sum(t_{ij}-u_{ij})^2$ over all 16 blocks. The rotation bound gives $\sum t_{ij}^2\le8q^2+1$. Let $\alpha,\beta$ be the numbers of actual $A,B$ sites in the two target blocks. Disjointness gives $\alpha+\beta\le e$. The scalar product $\sum u_{ij}(t_{ij}-u_{ij})$ equals
$$
 -qe+\frac{-(q-1)\alpha-(2q-1)\beta+(2q-1)e}{9}\ \ge -qe .
$$
Consequently $W\le (10q+6)/9+2qe$ by expanding the square and inserting the displayed reference values.

For the lower bound, on the 11 blocks outside the five selected full classes put $d_{ij}=9(t_{ij}-u_{ij})/q$. Its three row sums vanish. Each unit comparison with centers in $A$ or $B$ takes the form $\sum h_j(d_{ij}-d_{Cj})=-O$, where $i$ is the other full-block fiber and $O$ is the integer gap from the seven-block reference. This system requires no pointwise ratio comparison on the two target blocks. Its least squared solution norm divided by 81 gives a lower bound on $W/q^2$. Among 38,610 choices the verifier finds 37,290 consistent systems, with minimum $68585/462186$. At $q=2^{26}$ the two bounds force the stated integer deficit. [Finite certificate](../../../scripts/probes/probe_split_pencil_dense_blocks.py) · [Lean arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/SplitPencilBlockVariance.lean)
