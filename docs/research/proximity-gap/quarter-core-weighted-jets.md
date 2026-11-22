# Lower interpolation orders on three rich cores at quarter rate

On every injective domain of length $n=2^{30}$ in the second named prime field, the closed ball at **525,150,000 errors** meets the 128-bit line-MCA budget at rate $1/4$ and every positive width. The written upper bound is **2,081,389,015** bad scalars, against a budget of $2n=2,147,483,648$. On the named subgroup the first failing count is in **[525,150,001, 553,648,129]**. The lower bound advances by 450,000 error counts. [Earlier window and geometric assumptions](tangent-head-windows.md) · [Lean upper-endpoint witness](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimePlanarQuartet.lean)

## The residual surface

Write $e=525150000$, $t=n-e=548591824$ and $d=n/4-1=268435455$. Select one bad polynomial witness per bad scalar. The two ordinary Hasse interpolants have shapes $(11,22,21569)$ and $(22,44,379)$, with coefficient surpluses 7,694,423 and 2,503,215,374. Here a shape lists the multiplicity, value degree and total scalar/value degree. Allow at most 21,569 scalar-only labels. A primary factor with more than $L=2,051,368$ assigned labels divides the companion, by the resultant bound $21569\cdot44+22\cdot379<L$. For a value-linear factor above the cutoff the identity-site test gives an affine polynomial head. Its joint core has at least $C=t-255$ sites, since a head missing at least 256 agreements has at most $1+\lfloor e/256\rfloor=L$ assigned labels. The core consists of sites where both received rows equal the two defining polynomials. [Factor and affine-head tests](hodge-section-variance.md#production-specialization)

Let $j$ be the number of such rich affine heads. Assign to one of them every chosen witness lying on any such head. This keeps their cores fixed and leaves every other selected witness outside all of them. For $j\ge3$ choose three cores $A,B,C_0$. Their sizes are at least $C$, their pair intersections have size at most $d$, and every polynomial witness outside these heads meets each core on at most $d$ of its agreements. For the last assertion, subtract the head polynomial at the chosen scalar from the witness. This nonzero polynomial has degree at most $d$ and vanishes at those agreements. The new surface only needs to contain these outside sections.

At a site belonging to $m$ of the three cores require mixed-jet order $23-2m$. On any outside witness's agreement set $S$ the order sum is at least $23t-6d=11,006,999,222$. Call this weight cutoff $W$. Take value degree at most 40, total scalar/value degree at most 301 and coordinate/value weight strictly below $W$. The number of available coefficients is 66,730,729,902,264. For $b$ jet orders the site uses
$$
F(b)=\sum_{h=0}^{b-1}(b-h)(302-h)
$$
scalar-coefficient constraints. At $b=23,21,19,17$ this gives 81,328, 68,222, 56,240 and 45,390. These four values imply
$$
F(23-2m)+13106m\le81328+1208\binom m2.
$$
Summed over all sites the right-hand correction is at most $1208\cdot3d$, and the linear term on the left is at least $13106\cdot3C$. There are at most 66,728,561,841,250 constraints. The surplus of **2,168,061,014** produces a nonzero third surface. Substitution of any outside witness gives a polynomial of degree below $W$ with at least $W$ zeros counted with multiplicity. It therefore vanishes identically. Lean constructs this surface on the actual received rows. [Variable-order interpolation](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorJetInterpolation.lean) · [Core counts, root bound and surface](../../../ArkLib/Research/ProximityGap/Frontier/QuarterCoreWeightedJets.lean)

## Counting the factors

A residual primary factor with more than $L$ remaining labels divides the third surface when $j\ge3$, since $21569\cdot40+22\cdot301<L$. Its total scalar/value degree is therefore at most 301. For a factor of value degree $b$ in a primary of total value degree $l$, apply the tangent-head population estimate with
$$
W_b=11t-1-(l-b)d,\qquad
m_b=\begin{cases}379-j&j<3,\\ \min(379-j,301)&j\ge3.\end{cases}
$$
The $j$ rich affine heads divide the ordinary companion, which accounts for its remaining degree $379-j$. All three surfaces and their projections use the same two received rows. The characteristic of the named prime exceeds the discriminant and ramification degree bounds in the geometric estimate. [Tangent population estimate and hypotheses](tangent-head-windows.md#the-cap)

The rich heads contribute at most $j(e+1)$. Since $3C>n+2d$, every triple of rich heads is collinear over the rational function field. For $j\ge3$ the core union has size at least $U=\lceil jC^2/(C+(j-1)d)\rceil$, giving the additional bound $jn-(j-1)U$. A site in that union gives at most one fresh scalar across the heads, and a site outside it gives at most $j$. Apply the smaller of the two bounds and charge the scalar-only factors separately.

Over all 276 choices $0\le j\le l\le22$ and all partitions of $l-j$, the largest sum is 2,081,389,015, from three rich heads and one factor of degree nineteen. This proves the scalar count. Interleaving stability gives the stated threshold bound for every positive width. Lean checks the numerical tests, both ordinary surfaces, the variable-order residual surface, the polynomial overlap bound and the implication from the factor prices to the literal budget. The geometric step giving the nonlinear factor its price is the written normalized-surface argument of Theorem D′. [Exact numerical reproduction](../../../scripts/probes/probe_quarter_core_weighted_jets.py) · [Lean certificates](../../../ArkLib/Research/ProximityGap/Frontier/QuarterCoreWeightedJets.lean) · [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)
