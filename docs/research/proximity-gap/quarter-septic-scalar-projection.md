# Scalar projections in a two-sheet lift of a cubic quartet

A saturated degree-seven quartet on the 32nd roots cannot preserve the lifted pair equalities of any balanced sixteen-site cubic template even in a single nonzero scalar projection. The same holds for the asymmetric cubic with opposite multiplicities $3,2,1$. Consequently the quartet must change at least **six of the twenty-four** old planar pairs. This improves the general distance bound of five at this length. The result holds at both designated primes, in characteristic zero, and over splitting primes $p>2^{768}$. Saturation here means 28 distinct labelled double sites, four singleton sites, and four nonzero triangle determinants each having its 14 simple double-site roots. The existence of such a septic quartet remains open. [General distance bound](quarter-saturated-label-distance.md) · [Exact computation](../../../scripts/probes/probe_septic_scalar_projection.py)

## Why a projected row would give a fractional linear map

Subtract the zeroth head and take an arbitrary nonzero scalar linear combination of the two new rows. Suppose this row satisfies the old pair equalities at all 24 sites above the twelve old double sites. Separate the row into its even and odd parts in $X$. The two cubic rows in $X^2$ then separately satisfy every one of the twelve base constraints because the characteristic is odd. The scalar solution space modulo the common row has dimension two. Choose its basis $U,V$. The projection therefore has the form
\[
 (a+bX)U(X^2)+(c+dX)V(X^2).
\]
The two homogeneous linear multipliers cannot have a common projective zero. Otherwise all four projected heads coincide there, forcing every triangle determinant of the original planar quartet to vanish there. Each triangle has only its own fourteen finite roots, and no site belongs to all four zero sets. At infinity the determinants have degree exactly fourteen. This also excludes an identically zero projection.

Thus $M(X)=(c+dX)/(a+bX)$ is a nonconstant Möbius map. Apply a constant basis change so that all nonzero pair differences of the old planar values have a nonzero second coordinate. For a pair with base difference $(u,v)\ne(0,0)$, the projected pair coincides at $x$ precisely when $M(x)=-u/v$. At each of the eight sites over the four base holes this gives at most six choices. A saturated quartet must use at least four of the eight as double sites because it has 28 doubles in all. By the general bound, at most 19 of its doubles can keep their old pair. It therefore needs at least nine sites at which $M$ hits a slope of a pair with nonzero base difference.

Enumerate triples of hole inputs and distinct allowed slopes on them. Each triple determines its unique projective map by the cross ratio. Deduplicate these matrices, then check every one at all 32 sites. The 1,344 balanced oriented templates have 28 representatives under rotations, inversion and head permutations in this enumeration; the asymmetric cubic supplies one further representative. Across the 29 representatives there are exactly **72** choices of a representative and a map hitting at least four old hole sites. All hit exactly four, and **none hits any additional site**. Therefore there is no such projected row. If precisely nineteen labelled pairs were preserved, both residual row pairings in the general distance proof would be scalar multiples of the same degree-nineteen locator. Some nonzero scalar projection would then satisfy every original pair equality, which was just excluded. [Base splines](quarter-sixteen-splines.md) · [Residual-row theorem](../../../ArkLib/Research/ProximityGap/Frontier/SaturatedFaceLabelDistance.lean)

## Field transfer and reproducibility

The computation runs over both named fields, over $\mathbb F_{65537}$, and over the prime $p_*=553\cdot2^{768}+1$. The power $3^{(p_*-1)/2}\equiv-1\pmod{p_*}$ certifies primality by Proth's theorem: every prime divisor of $p_*$ is $1$ modulo $2^{768}$, by the order of 3, and exceeds $\sqrt{p_*}$.

Over $\mathbb Z[\zeta_{32}]$ each scalar degree-seven equality is a row with 24 columns after subtracting the zeroth head. At most sixteen entries are nonzero and every nonzero entry has absolute value one under every complex embedding. Each square minor has absolute value at most $4^{24}$, hence absolute norm at most $2^{768}$. All ranks of the original constraints with any specified alternate equalities therefore agree between characteristic zero, $p_*$ and any splitting prime larger than this bound. The equality and nonvanishing of the base pair directions likewise transfer by the smaller sixteen-site bound. In particular three distinct targets at three distinct hole sites specify a one-dimensional subspace of the four-dimensional old scalar kernel. The map they define hits a prescribed fourth or later pair exactly when its row leaves the rank unchanged. This proves the claimed transfer without computing characteristic-zero approximations. [Sixteen-site norm bounds](quarter-opposite-edge-characters.md)

Run `python3 scripts/probes/probe_septic_scalar_projection.py` to check all four fields, the primality witness and the two enumerations.

## Three independent Möbius transforms of powers are insufficient at length 32

In the three-slope construction let $m_1+m_2+m_3=7$ be the slope degrees. Each pair must coincide on $m_i+m_j$ distinct sites and coincide after the common involution on a disjoint set of that same size. Suppose all three slopes have the form $M_i(X^{m_i})$, with independent invertible Möbius maps. A constant slope forces each other positive $m_j$ to divide 32, since one entire fiber of $X^{m_j}$ must have $m_j$ sites there. The remaining degrees cannot sum to seven with this property. For positive degrees, there are four unordered possibilities.

| Degrees | Obstruction already from an unsigned coincidence |
|---|---|
| $1,1,5$ | A Möbius transition from $X$ to $X^5$ hits at most 4 sites; 6 are required. |
| $1,2,4$ | A transition from $X$ to $X^4$ hits at most 3; 5 are required. |
| $1,3,3$ | The two cubic powers have the same input. A nonidentity Möbius map has at most two fixed points, and $X^3$ permutes the subgroup. Identical slopes cannot have a finite coincidence divisor. |
| $2,2,3$ | A transition from $X^2$ to $X^3$ hits at most 3; 5 are required. |

For each of the three enumerated pairs the graph points $(x^a,x^b)$ are distinct. The computation tests every Möbius map specified by three points with distinct sources and targets. Maps with fewer hits cannot change the maxima. Each fourth-point test is rank of the four rows $(1,x^a,x^b,x^{a+b})$. Every four-row minor has absolute norm at most $16^{16}=2^{64}$, which transports this part to all splitting primes $p>2^{64}$ as well as characteristic zero. The obstruction allows arbitrary Möbius coefficients over extensions of these fields. [Three-slope reconstruction](quarter-three-slope-reconstruction.md) · [Production bounds for powers](quarter-slope-power-barrier.md)
