# Symmetries of four heads at the eighth-rate boundary

On the second named prime's subgroup of order $n=2^{30}$, a failure at **671,088,640 errors** forces a quartet whose directions change under every rotation of order at least sixteen. Even after choosing a constant projective change of direction coordinates and permuting the four heads, at most **268,435,454** sites can match all six side directions. One particular side fails the prescribed comparison on at least **805,306,370** sites. This leaves the first failing error count in **[671,088,640, 679,477,248]**. A generic quartet can escape these symmetries. [Unrestricted bounds and exceptional profiles](eighth-rich-head-safety.md#at-exactly-five-eighths)

More precisely, write $H$ for the designated subgroup, $k=n/8$, $d=k-1$, and $W_i=(A_i,B_i)$ for the four rich polynomial heads with no three collinear over the function field. A covariance consists of a rotation $x\mapsto\zeta x$, a **single constant** element $g$ of $\mathrm{PGL}_2$ over the algebraic closure, and a permutation $\pi$ of the four heads. For each of the six edges the rotated direction $[W_i(\zeta X)-W_j(\zeta X)]$ must agree with $g[W_{\pi i}(X)-W_{\pi j}(X)]$. At individual sites we test the determinant, so a vanishing vector counts as a match. For labeled heads ($\pi=1$) even a quarter turn is impossible. For the antipode the identity action on directions is impossible. Its only surviving labeled action is a nonscalar involution with a saturated quartet on the subgroup of half the size.

## Primitive polynomial coordinates

Let $C_i$ be the full joint agreement core of $W_i$, let $I=\sum_i|C_i|$ and put $s=n+4d-I$. A failure requires sorted deficits $(1,1,1,q)$ with $s\le q-1\le4$. Four rich heads leave an allowance of at most 20,607,410 labels on all other factors. Every bad scalar represented by a head has a fresh agreement away from that head's joint core. [Core and residual estimates](eighth-rich-head-safety.md#at-exactly-five-eighths)

First take $\pi=1$. Translate by $W_0$ and divide all six coordinate differences from that origin by their common polynomial gcd $h$, of degree $r$. The resulting three vectors $U_i$ are collectively primitive. Choose a constant invertible matrix representing $g$. Each $U_i(\zeta X)$ is proportional over the function field to its transformed vector. For two of these vectors, parallelism for the side joining their ends forces the two scales to agree because the vectors are independent. This gives one common rational scale for all three. Both polynomial tuples are primitive since rotation is a polynomial-ring automorphism and the representing matrix is invertible. Bézout in each tuple shows that the scale and its inverse are polynomials. Thus the scale is a nonzero constant. Absorb it into the matrix $M$ to obtain $U_i(\zeta X)=M U_i(X)$.

If $\zeta$ has order $l$, two independent vectors give $M^l=1$. In the odd characteristic here $M$ is diagonalizable for $l=2,4$. A component in the eigenspace of $\zeta^j$ uses only powers congruent to $j$ modulo $l$, by comparing coefficients. Primitivity forces one exponent class to be zero, as otherwise $X$ divides the tuple. In constant coordinates the differences therefore have the form
$$
 h(X)\big(A_i'(X^l),\ X^j B_i'(X^l)\big),\qquad 0\le j<l.
$$
For a scalar action take $j=0$. Put $a=\max_i\deg A_i'$ and $b=\max_i\deg B_i'$. Both rows are nonzero because the heads span a plane. Then $la+r\le d$ and $lb+j+r\le d$.

Off the roots of $h$ each of the four triangle determinants has the form $h^2X^j T(X^l)$ with $T\ne0$ of degree at most $a+b$. Since $0\notin H$, its total root multiplicity there is at most $l(a+b)$. At a site with $w$ owners the four triangle multiplicities total at least $2(w-1)$, by subtracting agreeing rows. At the at most $r$ sites with $h=0$ there are at most three excess owners per site. Consequently
$$
 I\le n+3r+2l(a+b).
$$
The same argument before separating powers gives $I\le n+3r+4(d-r)$ and hence $r\le s$. [Triangle multiplicities](four-arbitrary-head-cap.md#core-multiplicity) · [Quotient incidence theorem on actual agreement cores](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean)

## When opposite sites have the same directions

Suppose $l=2$ and $g=1$. Outside the roots of $h$, the evaluated configurations at $x$ and $-x$ differ by a translation and a nonzero scalar. In particular they determine the same set of geometric points up to this correspondence and have the same projective directions between corresponding points.

Write $x_j$ for the number of sites with $j$ owners. Incidence counting gives $x_2+2x_3+3x_4+s=4d+x_0$. The four full triangle degrees give $2x_2+5x_3+8x_4\le8d$, so $2x_0+x_3+2x_4\le2s$. There are at most $r+x_0+x_3+x_4\le12$ antipodal pairs containing a locator root or a site with owner count outside $\{1,2\}$.

For any other pair, let the owner multiplicities at its two sites be $w,w'$ and let $M$ count the distinct fresh projective directions available over the pair. At a covered site every fresh direction joins its received point to a different head point. If the two centers correspond, there are at most $4-w$ directions and $w=w'$. If the centers differ, the configuration has at most $6-w-w'$ distinct points. Their two sets of directions both include the line joining the centers. Together they give at most $2(6-w-w')-3$ directions. In either case $2M+3(w+w')\le16$. A pair with exceptional sites satisfies $2M+3(w+w')\le40$ since it has at most eight fresh slots and eight incidences. This count includes the projective direction at infinity and therefore bounds all finite labels.

Sum over $n/2$ pairs and use $I\ge n+4d-4$. The total number of distinct labels on the quartet is at most **1,879,048,348**. Even with every residual factor included the count is at most **1,899,655,758**, below $2n$. Lean checks the two sets of directions with arbitrary point multiplicities and the sum over the antipodal pairs. [Finite direction count](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean)

## Quarter turns and the surviving antipodal quotient

For a labeled quarter turn acting nonscalarly, $1\le j\le3$. The inequalities $4a+r\le d$, $4b+j+r\le d$ and $4d-4\le3r+8(a+b)$ have no nonnegative integer solution. A scalar quarter turn gives the already excluded identity action on applying the turn twice.

For a nonscalar antipode the inequalities become $2a+r\le d$, $2b+1+r\le d$ and $4d\le3r+4(a+b)+s$. They force
$$
 r=0,\quad s=4,\quad q=5,\qquad a=b=67,108,863.
$$
Equality in the quotient triangle budget forces every site to have one or two owners. All four triangle root budgets are filled. Each coincidence must be an owned double, with precisely the two triangles through its pair having simple zeros. An extra coincident pair, a third collinear point at a double in a triangle that does not contain both owners, or an unused root would spend multiplicity beyond equality. Paired sites have the same equality pattern by the nonsingular action. In particular both sites of any orbit containing a coincidence use the same double.

The four quotient heads $(A_i'(Y),B_i'(Y))$ on $H^2$ thus have exactly $4d'$ double sites with $d'=67,108,863$. In fact each full triangle has $2d'$ distinct simple roots on $H^2$. Summing the pair counts in the four triangles shows that opposite edges have equal counts and each vertex owns $2d'$ doubles. All remaining cells have four distinct evaluated points. They can be assigned as singletons, $k'+1$ per head, where $k'=d'+1$. This gives a saturated quartet with joint cores of size $3k'-1$ at length $8k'=2^{29}$ and dimension $k'$. Equivalently, the product of its four nonzero triangle determinants is, up to a scalar, $Q(Y)^2$ for a squarefree degree-$4d'$ divisor $Q$ of $Y^{2^{29}}-1$. Existence of this quotient incidence configuration is a necessary condition for the nonscalar case. Its existence alone supplies no count of distinct bad labels.

## Rotations with a permutation of the heads

For any permutation of four objects, $\pi^{12}=1$. If $\zeta$ has order $2^m\ge16$, iterating a proposed covariance twelve times gives a labeled covariance with rotation of order $2^{m-2}\ge4$. A further power gives a labeled quarter turn, which has been excluded. Thus one of the six polynomial comparison determinants is nonzero. Its degree is at most $2d$ after the constant change of coordinates and input rotation. It vanishes on at most $2d=268,435,454$ sites of $H$. This proves the claimed mismatch even when the proposed action originally matches only a subset. At order eight a permutation of order one, two or three is also excluded by taking its order as the exponent and, if necessary, taking another power to reach order four.

The stabilizer of $H$ in the domain projective line consists of rotations and inversions. Indeed an invertible fractional linear transformation preserving $H$ gives $(aX+b)^n-(cX+d)^n=\lambda(X^n-1)$. The scalar is nonzero by nonconstancy. If all four entries are nonzero, comparison at powers one and two gives $a/b=c/d$, impossible since $p>n$. A zero entry forces the matrix to be diagonal or antidiagonal by the same coefficients. Thus the subgroup of domain symmetries realizable by a constant direction action and relabeling for a surviving quartet has at most sixteen elements, at most eight rotations and one coset of reflections.

Lean checks primitive scale cancellation, the character of every nonzero coefficient, the triangle factorization and root multiplicities, the quotient budget for actual four-head cores, the finite direction counts, the degree cases, the permutation exponent, and the sampled determinant root bound. The assembly from projective covariance and the saturated quotient classification above is written. [Lean theorems](../../../ArkLib/Research/ProximityGap/Frontier/EighthDyadicHeadDirections.lean)
