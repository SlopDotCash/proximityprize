# Exact list thresholds from non-dihedral transpositions

Let $D$ be a smooth multiplicative coset of size $n$, let the Reed–Solomon dimension be $k$, and write $r=n-k-3$. Suppose a non-dihedral projective involution exchanges at most $T$ disjoint pairs of sites. Define
$$
M(e)=\binom e2-\lfloor e/2\rfloor,\qquad
L=M(r+1)(k+1),\qquad
U=\max\left(1,\left\lfloor\frac{T\binom nr}{L}\right\rfloor\right).
$$
For $r\ge2$ and $r\le k$, every center has list size at most $U$ through $r+1$ errors at every finite interleaving width. The same formula holds when $k\ge6144$ and $r+1\le16k$, which includes all four sponsor rates at production length. If $U\le B$ and $nB<\binom n{k+1}$, the exact first over-budget error count is $r+2=n-k-1$. In particular this holds for the sponsor budget $B=\lfloor p/2^{128}\rfloor$ whenever it lies in the indicated interval. [Threshold theorem](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListThreshold.lean) · [Binomial inequalities](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListArithmetic.lean)

## Weighted samples

Fix an $r$-site puncturing set and keep its $k+3$ complementary sites. A list member with exactly two errors on the retained sites determines a base pair $u,v$. Any other such member has a disjoint pair of errors $a,b$. Their difference vanishes at the remaining $k-1$ sites and is a scalar multiple of the corresponding locator. Consequently every alternative pair satisfies $f(a)f(b)=t$ for the same $t$, where $f(x)=(u-x)/(v-x)$. Give this incidence weight one if the base pair is nonantipodal and $t\ne u/v$, and weight zero otherwise. The base pair and all alternative pairs lie on the conic
$$
(1-t)xy-(u-tv)(x+y)=tv^2-u^2.
$$
Its determinant test gives $t(u-v)^2\ne0$. The exclusions rule out both inversion and negation, so at most $T$ members can have positive weight in the puncture. [Conic reduction](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListTranspositions.lean) · [Puncture bound](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListSampling.lean)

For a fixed word with $e$ errors, choose a nonantipodal error pair, delete the other $e-2$ errors, and add $r+2-e$ correct sites to the puncturing set. On fixing all but the final correct site, $k+2$ choices remain and the target becomes $\mu/f(x)$ for a fixed nonzero $\mu$. Injectivity of $f$ excludes at most one final site. After averaging, the word receives at least
$$
M(e)\binom{n-e}{r+2-e}\frac{k+1}{k+2}
$$
units of weight. For $3\le e\le r+1$ the stated parameter ranges make the minimum occur at $e=r+1$, where it is $L$. A word with at most two errors forces uniqueness by minimum distance. Double counting proves $U$. The prescribed-product construction exceeds $B$ at the next error count. [Double count and scalar estimate](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListBound.lean)

## All widths

Map each vector $(v_j)_{j<m}$ to $\sum_j v_j Z^j$ in the rational-function field $F(Z)$. This injects list members into the scalar Reed–Solomon code over $F(Z)$ on the same domain. Every realized pair product is already in $F$, so the pair cap survives the extension. The resulting estimate applies at every positive width without requiring any bound on the list size relative to the field order. [Canonical width transfer](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved/AgreementBounds.lean) · [Preservation of pair fibers](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListBound.lean)

On every proper smooth coset of a prime field, the Euler estimate supplies $T=\lfloor(n+1)/3\rfloor$. This alone can exceed the elementary puncture cap $\lfloor(k+3)/2\rfloor$ at the sponsor rates. At length 128 and prime order at least $2^{128}$ the sharp conic classification supplies $T=3$. The full weighted histogram gives a stronger numerical result at that length. [Euler estimate](../../../ArkLib/Research/ProximityGap/Frontier/DenseMobiusTranspositions.lean) · [Sharp classification](../../../ArkLib/Research/ProximityGap/Frontier/Smooth128Involutions.lean) · [Full histogram](dyadic128-two-error-slices.md)

## Production length

For $n=2^{30}$ and $p>2^{40}$ the certified Stepanov graph estimate bounds the number of sites a non-dihedral map carries back to the normalized subgroup by 3,960,117. Every transposition consumes two distinct sites, so $T=1,980,058$ works on every smooth coset. The graph theorem includes maps with zero entries in their matrices. Consequently the sampling estimate gives the following first over-budget counts whenever $U\le B$ and $nB<\binom n{k+1}$ for the indicated dimension. The sponsor choice is $B=\lfloor p/2^{128}\rfloor$. [Production theorem](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListMobius.lean) · [Stepanov graph bound](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

| Rate | Dimension | First over-budget error count |
|---|---:|---:|
| 1/2 | 536,870,912 | 536,870,911 |
| 1/4 | 268,435,456 | 805,306,367 |
| 1/8 | 134,217,728 | 939,524,095 |
| 1/16 | 67,108,864 | 1,006,632,959 |

Compared at the same $k+2$ agreements with the bound obtained by giving equal weight to all two-error samples and using only their disjointness, the sufficient budget before rounding improves by factors of approximately 135.57, 67.78, 33.89 and 16.95. For the comparison the disjointness cap per puncture is $\lfloor(k+3)/2\rfloor$ and the endpoint row count is $\binom{n-k-2}{2}(k+2)$. The budget interval depends on the rate; the two named production fields lie below these near-capacity intervals.
