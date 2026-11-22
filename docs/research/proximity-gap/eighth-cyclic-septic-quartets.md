# Saturated septic quartets on the 64th roots

Let $H=\mu_{64}$ in the second named prime field and write $w$ for its generator. A saturated quartet here consists of four polynomial pairs $W_0,\ldots,W_3$ of degree at most seven. No three are collinear over the rational function field. There are 28 distinct double sites in $H$, each assigned to one of the six equalities $W_i=W_j$, with no two of the assigned equality sets intersecting. Such a quartet would provide a smooth eighth-rate attack at 675,282,945 errors by a common locator and a variable output shear. A full seven-site edge is impossible. A constant affine quarter turn cyclically permuting the heads is also impossible. These results leave arbitrary septics open.

## The largest possible edge

Write $e_{ij}$ for the edge sizes. Each triangle determinant is nonzero of degree at most 14. Every double site is a zero of the two triangles containing its edge. The four triangle bounds sum to 56, exactly twice 28. Each triangle therefore uses all 14 roots, and any site away from its three assigned edges has nonzero determinant. Subtracting the four triangle size equalities gives equality of opposite edge sizes. The three sizes at a vertex sum to 14.

Suppose $e_{23}=7$. Both coordinate differences $W_2-W_3$ are constant multiples of the same monic degree-seven vanisher. Take a constant linear form annihilating their direction, and denote its values on the heads by $f_0,f_1,f_2=f_3$. Noncollinearity of triangles 023 and 123 gives $f_0,f_1\ne f_2$. If $f_0=f_1$, the difference $f_2-f_0$ vanishes on the fourteen sites of the four edges connecting these two pairs, which exceeds its degree. The three nonzero polynomials $P=f_1-f_0$, $Q=f_2-f_0$ and $Q-P$ vanish respectively on edge 01, on edges 02 and 03, and on edges 12 and 13. Their three root sets are disjoint and have seven sites each. This gives a rational function $Q/P$ with three disjoint full fibers, excluded by the exact named-field septic census. The projection argument holds over arbitrary finite fields and in every degree. [Lean projection theorem](../../../ArkLib/Research/ProximityGap/Frontier/SaturatedQuartetFullEdge.lean) · [Full-fiber census](eighth-quotient-septic.md#the-finite-field-test)

The possible edge-size triples thus reduce to $(2,6,6),(3,5,6),(4,4,6),(4,5,5)$. For rational direction maps whose degrees are seven minus the opposite edge sizes, the remaining degree profiles are $(1,1,5),(1,2,4),(1,3,3),(2,2,3)$.

## A cyclic permutation of the heads

Set $\iota=w^{16}$. Suppose $W_{i+1}(X)=T W_i(\iota X)+L(X)$, with indices modulo four, one constant invertible matrix $T$ and one common polynomial translation $L$. Subtract the centroid of the four heads at every $X$ to remove $L$. The resulting heads span a plane, so $T^4=I$ and $T$ is diagonalizable over the named field. Write its eigenvalues as $\iota^{-r}$.

At $X=0$ each triangle determinant is nonzero, since its fourteen roots lie in $H$. An eigenvalue 1 gives a constant coordinate on the four-point orbit, which would put the heads on a line. At infinity the leading degree-seven vectors of each triangle are also noncollinear, since its determinant has degree fourteen. The order-four operator on these vectors is $\iota^7 T$, excluding $r=3$. A scalar $T$ would likewise give a collinear orbit at zero. The two characters are therefore exactly $r=1,2$.

Let $a=e_{01}$ be the common size of the four adjacent edges. An opposite edge has size $14-2a$, so $a$ is 4, 5 or 6 by the seven-site exclusion. Write $D$ for the monic vanisher of the adjacent support. Its roots occupy distinct orbits of the quarter turn. Rotate once to put one at exponent zero, and take the lexicographically first exponent tuple among all translates with that property. For a character row $f$, there is a polynomial $K$ of degree at most $7-a$ with
$$
f(X)-\iota^{-r} f(\iota X)=D(X)K(X).
$$
The coefficients at exponents $r$ and $r+4$ in $DK$ must vanish. The opposite edge condition at $x$ further requires $(DK)(x)+\iota^{-r}(DK)(\iota x)=0$. Its roots come in antipodal pairs. The two characters must both have a nonzero $K$ satisfying these equations on the same $7-a$ representatives, all in distinct unused quarter-turn orbits. If $K=0$, the four heads have the same character coordinate and are collinear.

| Adjacent size $a$ | Opposite size | Rotation representatives | Surviving supports |
|---:|---:|---:|---:|
| 4 | 6 | 7,280 | 0 |
| 5 | 4 | 69,888 | 0 |
| 6 | 2 | 512,512 | 0 |

The verifier computes both linear kernels over the named prime. In a two-dimensional kernel the selected evaluation rows must lie on a single line, allowing zero rows. In higher dimension it computes the rank for the selected representatives directly. [Reproduce both censuses](../../../scripts/probes/probe_mu64_cyclic_septic_quartets.py)

## Two reflection families of degree profile $(1,3,3)$

For three rational direction maps write $J(z)=-z$. Every pair must have disjoint full simple fibers of $R_i=R_j$ and $R_i=J(R_j)$ on $H$. Consider first the coordinate $t=(x-1)/(x+1)$ and maps $R_1=t$, $R_2=R(t)$, $R_3=-R(-t)$ for a cubic rational function $R$. The inversion $x\mapsto 1/x$ acts by $t\mapsto -t$. The positive representatives $t_i$ from exponents $1\le i\le31$ represent the 31 nonfixed pairs.

Let $P,Q$ be monic quartic vanishers of the sites where $R(t)=t,-t$, respectively. Their supports use eight distinct nonfixed pairs, because the reflected coincidences with $R_3$ must be disjoint. Neither $0$ nor infinity is one of these sites. Comparing leading coefficients and evaluating at zero gives $(R-t)/(R+t)=-P/Q$ and $P(0)=-Q(0)$. With signs forgotten the two index sets $A,B$ thus have equal products $\prod t_i$ up to sign. Among disjoint four-element index sets there are 4,095 unordered pairs with this property. The required equality $R_2=-R_3$ holds at the two fixed points. At its four further sites the two products $\prod_{i\in A}(t_i^2-t^2)$ and $\prod_{i\in B}(t_i^2-t^2)$ must agree. Of the 4,095 pairs, 4,074 have no eligible index and 21 have one. Two are necessary.

For a second family, use $R_1=x$, $R_2=R(x)$ and $R_3=1/R(1/x)$ with the same $J$. The fixed and antifixed quartic supports of $R$ again project to two disjoint four-sets $A,B$ of indices modulo inversion. For $U=(R-x)/(R+x)$, the third map has transformed coordinate $-U(1/x)$. The condition $R_2=-R_3$ implies $-U(x)U(1/x)=1$. As $U=-P/Q$ and $P(0)=-Q(0)$, inversion of the two monic quartic products cancels the minus sign. Thus, with $y=x+1/x$ and $s_i=w^i+w^{-i}$,
$$
\prod_{i\in A}(y-s_i)=\prod_{i\in B}(y-s_i).
$$
Their difference has degree at most three. It cannot vanish identically for two disjoint index sets. Six distinct roots in $x$ require three trace values outside $A,B$, each with two distinct inverse images. Testing all 31 possible trace values gives 22,136 unordered support pairs with one matching value and 50 with two. None has three. Both reflection tests use the full production prime. Other involutions and direction maps remain possible.

## Consequence if an unrestricted quartet exists

Put $s=2^{24}$, so $n=64s$ and $k=8s$. Substitute $Y=X^s$ in the heads. A common locator of degree $s-2$ can be supported on a free fiber. The 28 double fibers give $14s$ sites to each head. The other $35s+2$ noncommon sites may be allocated as evenly as possible among the four. The smallest core then has $14s+(s-2)+35s/4=95s/4-2$ sites. A constant projection separates distinct values on the 64 fibers. A generic shear by $\theta X$ on the second coordinate preserves degree less than $k$ and distinguishes labels from different physical sites. Each nonsingular double site supplies two foreign heads and every private site supplies three, all with distinct directions by the triangle determinant count. The named field exceeds the number of forbidden parameters. The resulting $161s+6$ fresh labels would cross the budget at $64s-(95s/4-2)-1=675,282,945$ errors. This implication uses unrestricted septics as a hypothesis. The certified smooth upper endpoint remains 679,477,248. [Planar shear and bad-scalar proof](second-prime-four-noncollinear-cubics.md)
