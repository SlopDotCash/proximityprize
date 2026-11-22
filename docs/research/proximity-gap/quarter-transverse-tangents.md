# Quarter-rate safety from rational tangents and collinear cores

At rate $1/4$, length $n=2^{30}$ and tolerance $2^{-128}$, every injective domain over the second named prime is safe through **529,940,000 errors** at every positive width. On the named subgroup the first failing count is in **[529,940,001, 553,648,129]**. The safety proof allows at most 2,146,244,663 bad scalars. The upper endpoint is attained by a received pair whose count exceeds the budget. [Quarter-rate failure witness](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimePlanarQuartet.lean) · [Earlier determinant bounds](tangent-polar-windows.md)

The subsequent common-factor argument raises the lower endpoint to 533,150,001. [Shared companion degrees](quarter-common-factor-degrees.md)

## Cost of a tangent outside the common line

Suppose $j\ge3$ distinct polynomial heads of coordinate degrees at most $d$ lie on one line over the coordinate function field. Each has a joint core of at least $C$ sites against the same received pair. Write their line as $A+f(P,Q)$ with coprime polynomial direction $(P,Q)$ of degree $h$. Two of their cores overlap at most $d-h$ times. Their union $U$ obeys, for every integer $1\le a<j$,
$$
a(a+1)|U|\ge 2ajC-j(j-1)(d-h).
$$
Indeed the sum of the site multiplicities is at least $jC$, the sum of their ordered distinct pairs is at most $j(j-1)(d-h)$, and $(m-a)(m-a-1)\ge0$ for each covered multiplicity $m$. Since $a(a+1)\le j(j-1)$, put
$$
u_j=\left\lceil\frac{2ajC-j(j-1)d}{a(a+1)}\right\rceil.
$$
Then $|U|\ge h+u_j$. The ordinary Cauchy bound on $|U|$ also remains available. [Polynomial direction and pair intersections](../../../ArkLib/Research/ProximityGap/Frontier/EighthCollinearOutlier.lean)

Let a rational tangent have denominator $Z$ of degree at most $c_i$ and numerators $N_1,N_2$ of degrees at most $d+c_i$. Assume it is regular and equals the two received rows at $t-\ell_i$ or more sites. If the tangent lies outside the polynomial line, its determinant
$$
P(N_2-ZA_2)-Q(N_1-ZA_1)
$$
is nonzero. Every regular agreement in $U$ is a root. Its degree is at most $d+h+c_i$, so $t-\ell_i\le n-|U|+d+h+c_i$. Consequently each such tangent pays
$$
c_i+\ell_i\ge g_j:=t+u_j-n-d.
$$
This uses one polynomial for the entire union, including sites owned by several of the heads. The Lean cost theorem accepts tangent coordinates over an arbitrary extension of the base field and proves the inequality before division by $a(a+1)$. Rounding uses that the individual losses and degrees are integers. [Cleared tangent determinant and cost theorem](../../../ArkLib/Research/ProximityGap/Frontier/EighthCollinearOutlier.lean) For our parameters take $a=\lfloor j/2\rfloor$. The first three gaps, for $j=3,4,5$, are **27,722,887**, **114,891,153** and **119,511,592**, respectively.

For a nonlinear factor of value degree $b$, scalar/value degree at most $m$ and coordinate/value weight at most $W$, the logarithmic tangent estimate discards at most $G+2bm$ labels. With $A_X=(2b-2)W-b(b-1)d$ and $G=(2b-2)m-b(b-1)$, the retained tangents have
$$
\sum c_i\le H=2A_XG+2Wm,\qquad \sum\ell_i\le R=(G+m)n.
$$
There are at most $\lfloor(H+R)/g_j\rfloor$ retained labels with tangent outside the line. For the tangents on the line, the primal tangent lines pass through one fixed projective point. The degree-one polar gives at most $m(m-1)$ smooth primal points. The points are distinct because the selected scalars are distinct. The named characteristic exceeds both the discriminant weight and the plane polar degree bound. This gives a second component price alongside the existing Veronese determinant and ordinary tangent estimates, and one can take their minimum. The logarithmic height estimates and projective duality are written geometric inputs. [Tangent heights](logarithmic-section-heights.md) · [Polar intersection and irreducibility](tangent-polar-windows.md#a-determinant-bound-for-the-tangents)

## Applying the bound to one received pair

Here $d=268435455$, $t=543801824$ and $C=t-255$. Use the ordinary mixed Hasse surfaces of shapes $(19,38,37338)$ and $(37,74,1051)$. Assign one witness to one primary factor for each bad scalar. The strict cutoff is 2,802,951. Above it, the factor divides the second surface by the resultant bound. If it is value-linear, the identity-site test gives a polynomial head of core size at least $C$. All sets of three such heads are collinear since $3C>n+2d$. Assign every chosen witness on one of these rich heads to a single such head. At most 37,338 scalars arise from scalar-only factors.

When there are three or more rich heads, take three cores and require order $38-2m_x$ at each site with $m_x$ owners among the three. The resulting surface has value degree 70, total scalar/value degree 909 and coordinate/value weight below $38t-6d$. A conservative count gives 2,983,187,588 more coefficients than constraints. Keeping the exact pair penalty raises the surplus to 116,531,385,053. A remaining polynomial witness meets each chosen core on at most $d$ agreements, so the sum of orders over its agreements is at least $38t-6d$. This forces identical vanishing on every such section. The cutoff exceeds $37338\cdot70+38\cdot909$. A surviving factor above that cutoff divides this surface too. Lean constructs all three surfaces from the received rows and proves the residual vanishing directly for any three distinct rich heads. [Received-row construction](../../../ArkLib/Research/ProximityGap/Frontier/QuarterTransverseSurfaces.lean) · [Construction with variable orders](quarter-core-weighted-jets.md#the-residual-surface)

For total primary value degree $l\le38$ and $j$ rich heads, a remaining factor of degree $b$ has $W\le19t-1-(l-b)d$ and $m\le1051-j$. If $j\ge3$, also $m\le909$. Use the Veronese parameters $(s,a)=(7,5)$ for $j<3$, $(18,13)$ for $j=3$ and $(1,1)$ for $j\ge4$. When the actual scalar/value degree is at most $s(s-1)$, apply the degree-one polar instead. Take the maximum over these two degree ranges. For $j\ge3$ apply the transverse bound in both ranges. For the affine populations use $j(e+1)$ and also $jn-(j-1)|U|$ when the heads are collinear.

The 9,880 inequalities for positive residual degrees cover every partition. The largest bound is **2,146,244,663**, at three rich heads and a degree-35 factor. This leaves 1,238,985 labels below budget. Lean verifies the 2,146,244,663 bound from the factor prices; independent verified replay accepted 3,301 declarations for this calculation and the parameter tests. The integer probe independently reproduces the exact maximum, surface ranks and determinant tests. [Lean allocation certificate](../../../ArkLib/Research/ProximityGap/Frontier/QuarterTransverseTangentBudget.lean) · [Numerical reproduction](../../../scripts/probes/probe_quarter_transverse_tangents.py) · [Positive-width stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)
