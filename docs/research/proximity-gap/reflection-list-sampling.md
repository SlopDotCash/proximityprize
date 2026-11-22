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

For $n=2^{30}$ and $p>2^{40}$ the certified Stepanov graph estimate bounds the number of sites a non-dihedral map carries back to the normalized subgroup by 3,143,679. Every transposition consumes two distinct sites, so $T=1,571,839$ works on every smooth coset. The graph theorem includes maps with zero entries in their matrices. Consequently the sampling estimate gives the following first over-budget counts whenever $U\le B$ and $nB<\binom n{k+1}$ for the indicated dimension. The sponsor choice is $B=\lfloor p/2^{128}\rfloor$. [Production theorem](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListMobius.lean) · [Stepanov graph bound](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

| Rate | Dimension | First over-budget error count |
|---|---:|---:|
| 1/2 | 536,870,912 | 536,870,911 |
| 1/4 | 268,435,456 | 805,306,367 |
| 1/8 | 134,217,728 | 939,524,095 |
| 1/16 | 67,108,864 | 1,006,632,959 |

Compared at the same $k+2$ agreements with the bound obtained by giving equal weight to all two-error samples and using only their disjointness, the sufficient budget before rounding improves by factors of approximately 170.78, 85.39, 42.69 and 21.35. For the comparison the disjointness cap per puncture is $\lfloor(k+3)/2\rfloor$ and the endpoint row count is $\binom{n-k-2}{2}(k+2)$. The budget interval depends on the rate; the two named production fields lie below these near-capacity intervals.

## Graded Stepanov constraints

At derivative order $i<D$ the polynomial constraint has degree at most $A-1+2i$. There are $A+2i$ coefficient equations. For $J$ target cosets the total is $JD(A+D-1)$. A nonzero auxiliary exists whenever this is strictly below $BAC$. On a source subgroup of order $N$ and target subgroup of order $M$, the multiplicity bound is
$$
D|S|\le A-1+N(C-1)+M(B-1).
$$
Here $AC\le M$, $A\le N$, $D\le p$ and $A-1+N(C-1)<p$ ensure the Vandermonde and factorial tests in characteristic $p$. The estimate for one target holds for every non-dihedral projective map, including those with a zero matrix coefficient, by inverting input or output as needed. [Kernel and multiplicity proof](../../../ArkLib/Research/ProximityGap/Frontier/MobiusStepanov.lean) · [Multi-coset and graph estimates](../../../ArkLib/Research/ProximityGap/Frontier/MobiusSubgroupBound.lean)

When $N=M=n$ and $J^2u^3\le n$, setting $A=D=Ju^2$, $C=Ju$, $B=2Ju$ gives $|S|\le 1+3n/u$ under the stated characteristic assumption. At $J=1$ the resulting transposition bound applies to any smooth coset. At $n=2^{30}$, the choices $A=1{,}049{,}601$, $B=2{,}043$, $C=1{,}023$, $D=1{,}046{,}527$ give 2,193,654,544,389 variables and 2,193,653,500,929 constraints. The degree ceiling is 3,289,945,998,336. Dividing by $D$ and rounding down gives 3,143,679 matched sites, a reduction of 816,438 sites from the common-width count. Lean verifies the numerical bound and the list threshold. An exhaustive integer check proves that no positive $A,B,C,D$ meeting the same graded rectangular inequalities give a smaller degree-to-multiplicity floor at this $n$. That check allows every characteristic-compatible choice and even drops the characteristic condition. [Optimum verification script](../../../scripts/probes/probe_graded_stepanov_optimum.py)

## Weighted two-error list bound at arbitrary length

For a nonantipodal pair of sites $u,v$ let $f(x)=(u-x)/(v-x)$. Write $A(t)$ for the number of unordered pairs of distinct sites outside $u,v$ with $f(a)f(b)=t$. Assign a penalty $P(j)$ of zero for $j\le1$, one for $j=2$, and three for $j\ge3$. Suppose every such pair and every nonzero scale $\mu$ satisfy
$$
\sum_{x\ne u,v} P(A(\mu/f(x)))\le S.
$$
With $n=k+3+r$, $r\ge2$, $S<3(k+2)$ and $M(e)=\binom e2-\lfloor e/2\rfloor$, define
$$
U_S=\max\left(1,\left\lfloor\frac{6\binom nr}{M(r+1)(3(k+2)-S)}\right\rfloor\right).
$$
At most $U_S$ interleaved codewords lie in any ball through $r+1$ errors whenever the endpoint minimizes the row weight. The sufficient test is $r\le k$ or $M(r+1)(k+2)\le2\binom{2k+2}{k+1}$. The result holds over any field. On a smooth domain over a finite field, every positive interleaving width has first over-budget error count $n-k-1$ throughout the integer budget interval
$$
U_S\ \le B\ \le\left\lfloor\frac{\binom n{k+1}-1}{n}\right\rfloor.
$$
This is the interval where these upper and lower estimates meet. The first failure outside the interval requires a separate bound. [Weighted scalar, interleaved and threshold theorems](../../../ArkLib/Research/ProximityGap/Frontier/WeightedTwoErrorList.lean) · [Endpoint weight test](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListArithmetic.lean)

Each two-error incidence receives $3-P(A(t))$ units of credit. When the puncture contains $j$ list members, each of the other $j-1$ pairs gives an alternative for that member. Thus the column total is at most six in every multiplicity case. For a fixed nonantipodal error pair and the last of the punctured correct sites, the scale $\mu$ is fixed and $k+2$ choices remain. The total credit is at least $3(k+2)-S$. The row averaging argument now gives the displayed denominator. On extending the coefficient field, every realized nonzero scale is a product of three base-field ratios. All other nonzero scales have zero charge. Consequently the same cap works over the rational-function field used for arbitrary interleaving width. [Column bound](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSliceWeight.lean) · [Last-site bound](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSliceRows.lean) · [Scalar double count](../../../ArkLib/Research/ProximityGap/Frontier/ReflectionListBound.lean)

Compared with the transposition cap $T=3$, the ratio of the two sufficient budgets before integer rounding is $(3(k+2)-S)/(2(k+1))$. In particular $S=29$ improves the bound at every $k\ge26$. The geometric input $S=29$ has a written all-dyadic derivation. Under the coarse transfer condition $p>2^{7n/4}$, a dyadic length $n\ge256$ already has $n\lfloor p/2^{128}\rfloor\ge2^n\ge\binom n{k+1}$. In that range the list upper estimate improves at applicable dimensions and the prescribed-product lower bound does not determine the first sponsor-budget failure. [All-dyadic shape argument](dyadic-three-pair-shapes.md)

## A four-rate 64-site prime-field band

For every smooth 64-site multiplicative coset over $\mathbf F_p$ with $p>2^{112}$, the penalty is at most twelve. Normalize the coset coordinates with a primitive 64th root, and embed their exponents as even exponents in the 128-site orbit of the certified 237-bit field. The order-64 three-product norm bound transfers source collisions to this suborbit because $2^{7\varphi(64)}=2^{224}<p^2$. The target 128-site certificate controls all of its suborbits by the injective transfer theorem. This argument requires only the existence of the source 64th root. [Prime transfer and complete endpoint](../../../ArkLib/Research/ProximityGap/Frontier/WeightedList64.lean) · [Profile transfer](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSliceNormalize.lean)

In dimension 32 the resulting sufficient budget is $220{,}447{,}348{,}371{,}475$. The bounds from $S=29$ and $T=3$ are $271{,}784{,}402{,}101{,}819$ and $300{,}610{,}020{,}506{,}557$. For
$$
220{,}447{,}348{,}371{,}475\le B=\lfloor p/2^{128}\rfloor\le27{,}767{,}032{,}438{,}524{,}098
$$
the four exact first failures at every positive width are as follows.

| Dimension | First failing error count |
|---:|---:|
| 32 | 31 |
| 16 | 48 when $B<488{,}526{,}937{,}079{,}580$, otherwise 49 |
| 8 | 57 |
| 4 | 61 |

The 176-bit prime $p=441\cdot 2^{167}+1$ has $B=242{,}442{,}313{,}924{,}608$ and realizes the lower quarter-rate branch. Lean proves primality with Lucas witness 11, certifies a primitive 64th root, and verifies the list comparisons for all smooth orderings. The proof covers the sponsor's list-decoding predicate on these domains. The general proximity-gap and correlated-agreement assertions remain open. [Concrete prime and thresholds](../../../ArkLib/Research/ProximityGap/Frontier/WeightedList64.lean)
