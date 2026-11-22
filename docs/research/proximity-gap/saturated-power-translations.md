# Power direction maps at the eighth-rate successor

At $n=2^{30}$ and $d=n/8-1=134217727$, three independent Möbius transforms of powers cannot realize the saturated four-head profile $(1,1,1,1)$ on the named subgroup. This exclusion already follows from the six coincidence divisors, before counting fresh labels. If just one of the three maps is a Möbius transform of a power and the other two are arbitrary nonconstant rational functions, at least one companion has degree **7,479,698** or more. The unrestricted eighth-rate interval remains **[671088640, 679477248]**. [Successor reduction](eighth-rich-head-safety.md#at-exactly-five-eighths) · [Kernel-checked translation and degree bounds](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)

The same argument improves two quantitative restrictions for the quarter-rate seam on the same subgroup. Two transformed powers in an overrun have even degree sum at most **46,340**, down from 4,993,531. With one transformed power the larger of its two arbitrary companions has degree at least **27,117,488**. These restrictions permit independent target coordinate changes and coefficients in the algebraic closure. [Earlier quarter-rate bounds](quarter-slope-power-barrier.md)

## The six full coincidence divisors

Write $H=\mu_n$ and $J$ for the constant nonsingular involution on opposite side directions of a saturated quartet. There are three rational direction maps $z_i$ of degrees $m_i$ with $m_1+m_2+m_3=d$. For every $i<j$, each of $z_i=z_j$ and $z_i=Jz_j$ holds on exactly $m_i+m_j$ sites. The six divisors are simple, disjoint, and contained in $H$. In particular $z_1(0),z_2(0),z_3(0)$ are three distinct projective points. These facts use saturation of the triangle root budgets and the opposite-side identity. At eighth rate the remaining $n-4d$ sites are singletons. The argument for the six divisors only uses the full $4d$ double sites. [Opposite-side identities and exact divisor degrees](quarter-saturated-opposite-directions.md) · [Three-map coordinates](quarter-three-slope-reconstruction.md)

## The face map of a surviving quartet is birational

The four triangle determinants of a saturated quartet give a projective plane map of degree $2d$. A proper covering degree $q$ of its image divides $d$. Indeed the two scalar head rows are independent degree-$d$ syzygies of the signed minors, and every syzygy of degree at most $d$ is a constant combination of them. The degree splitting argument downstairs then forces $q\mid d$ and both rows descend up to a common scalar. This uses only saturation and applies with any number of singleton sites. All double sites in one covering fiber give the same two fresh directions. Fibers above a double site contain exactly $q$ distinct double sites: the faces containing its labelled edge vanish simply, and the pair stratum is the full common zero set of those faces. [Syzygy and covering argument](quarter-saturated-birational.md#why-a-rational-cover-repeats-fresh-labels)

The smallest prime divisor of $d=2^{27}-1$ is seven. A proper cover therefore contributes at most $8d/7$ distinct directions on all double sites. The $n-4d$ singletons add at most three each, giving a maximum of **1,764,004,436** head labels. Even after adding the full residual allowance of 20,607,410, the total is at most **1,784,611,846**. Thus a saturated first-failure candidate has a birational face map and at least **258,131,746 distinct double-site direction orbits**. The latter count follows from $2B+3(n-4d)+20607410>2n$. [Checked cover and orbit counts](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)

## A cyclic power graph

Take $z_i=M_i(X^a)$ and $z_j=M_j(X^b)$ with $a,b>0$. For either sign, conjugating by the two target maps gives a fractional-linear transition $T$ between $(x^a,x^b)$. Put $g=\gcd(a,b,n)$ and $s=a+b$. The graph $K=\{(x^a,x^b):x\in H\}$ is a cyclic group of order $n/g$, and the $s$ marked sites give exactly $s/g$ graph points on $T$. One coordinate is injective on $K$ because at least one of $a/g,b/g$ is odd. Interchange coordinates and invert $T$ if needed.

For any $(u,v)\in K$ other than $(1,1)$, a pair of marked graph points with that displacement yields a solution of $T(uX)=vT(X)$. There are at most two solutions unless this is an identity of projective maps. As $u\ne1$, an identity requires $v\ne1$ and $T$ carries the two fixed points of scaling by $u$ to those of scaling by $v$. Thus $T(X)=cX$ or $c/X$. The argument holds over every field containing the graph. Counting all ordered pairs of distinct marked graph points gives, for a transition outside these two forms,
$$
s(s-g)\le2g(n-g).
$$
Lean proves the group count and the quadratic intersection bound by clearing the Möbius denominator. [Translation theorem](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)

When $g=1$, the inequality gives $s\le46341$. Above the bound, both signed transitions must be toric. A scaling requires $x^{b-a}=c$, with fewer than $s$ solutions unless the maps coincide identically, which also contradicts the stated finite coincidence divisor. Thus both transitions are inversions. Each signed fiber is $x^s=c_\pm$, giving $s\mid n$. Moreover the quotient of the two transitions is the nonidentity order-two scaling, so $c_-=-c_+$. The pair of signed strata is then one multiplicative coset of $\mu_{2s}$.

Order the three positive degrees so that $a$ is largest. With $d=2^{27}-1$, both $a+b$ and $a+c$ exceed 46,341. If $a$ is even then at least one other degree is odd. The corresponding pair has $g=1$, but its odd degree sum exceeds one and cannot divide $n$. If $a$ is odd, both pairs have $g=1$. Each degree sum must be a power of two less than $2^{27}$, hence at most $2^{26}$. Together they sum to $d+a>2^{27}$, a contradiction. If one or two slopes are constant, every positive power degree itself must divide $n$, since its coincidence with a constant has that many subgroup sites. The integer $2^{27}-1$ cannot be a sum of at most two powers of two. This proves the eighth-rate exclusion.

For the quarter-rate overrun both power exponents are odd by the existing individual image estimate. If the two signed transitions are inversions and $s>46341$, each signed stratum is antipode-invariant. Its points $x,-x$ give the same $J$-orbit since $J$ is conjugate by $M_j$ to the scaling by $-1$ and $b$ is odd. Across the two strata this loses at least $s$ double-site orbits, while a quarter-rate overrun permits just one repeat. The non-toric bound gives $s\le46341$. Since $a,b$ are both odd, their sum is even and is therefore at most **46,340**. [Quarter-rate orbit budget](quarter-saturated-opposite-directions.md#coincidences-and-fresh-directions)

## One power and two arbitrary companions

Let $z_1=M(X^a)$ with $a>0$, and consider an arbitrary companion of degree $b>0$. On the $s=a+b$ unsigned coincidence sites the rational function $R=M^{-1}z_j$ equals $X^a$. For a displacement $u\in H$, $R(uX)=u^aR(X)$ has at most $2b$ solutions unless it is a rational identity. This follows by cross-multiplying two degree-$b$ pairs. If $s(s-1)>2b(n-1)$ there must be a nonidentity $u$ giving the identity. Its powers contain $-1$, so
$$
z_j(-X)=M\bigl((-1)^a M^{-1}z_j(X)\bigr).
$$
This also gives the corresponding identity for $z_1$. [General rational graph count](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)

Suppose both companions exceed their respective $2b(n-1)$ bounds. For odd $a$ all three maps transform under the same nonidentity projective involution. Evaluating at zero gives three distinct fixed points, which is impossible. For even $a$ the three maps are invariant under $X\mapsto-X$, so both unsigned coincidence sets with $z_1$ are antipode-invariant and have even size. Both companion degrees must then be even as well, contradicting the odd total $d$.

Consequently one companion, with degree $b$ and $s=a+b$, satisfies $s(s-1)\le2b(n-1)$. If $B$ is the larger companion degree then $s\ge d-B$ and $b\le B$. The necessary inequality $(d-B)(d-B-1)\le2B(n-1)$ first holds at $B=7479698$ for eighth rate and $B=27117488$ for quarter rate. No assumption about fresh-label distinctness is needed for this last argument. [Checked integer bounds](../../../ArkLib/Research/ProximityGap/Frontier/PowerSlopeCoincidences.lean)
