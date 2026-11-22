# Outside witnesses above the exact sixteenth-rate window

At the second named prime, every injective evaluation domain of length $n=2^{30}$ satisfies the following bounds on the first MCA failure, at every positive width. Each row holds for every integer dimension from two through the dimension shown. The common upper bound is **715,827,882**. The exact answer through dimension **71,582,789** was established earlier. [Exact window](three-heads-above-one-sixteenth.md) · [Three-head upper witness](../../../ArkLib/Research/ProximityGap/Frontier/ExceptionalHeadLocatorMass.lean)

| Maximum dimension | First failure at least | Maximum dimension | First failure at least |
|---:|---:|---:|---:|
| 71,582,790 | 715,827,881 | 77,686,751 | 715,827,876 |
| 71,582,792 | 715,827,880 | 77,734,913 | 715,827,875 |
| 73,688,168 | 715,827,879 | 77,768,622 | 715,827,874 |
| 76,695,850 | 715,827,878 | 77,782,879 | 715,827,873 |
| 77,650,737 | 715,827,877 | 77,807,386 | 715,827,872 |

## Extracting the outside witnesses

For each row put $d=k-1$, take $e$ one below the claimed first failure and write $t=n-e$, $c=t-1$. Use the double mixed interpolant of value degree seven and scalar/value degree 25 with coordinate weight at most $2t-1$. A single interpolant at $d=77,807,385$ and $t=357,913,944$ also suffices for the entire table by monotonicity of its degree and agreement restrictions. The logarithmic section estimates give at most 140,215 labels on each nonlinear component using the parameters of its row. Take the large-head cutoff 500,000. The affine extraction, collinear-core union estimates and remaining degree allocations from the preceding three-head proof hold with this cutoff in all ten rows. The verifier recalculates every inequality. An overrun requires exactly three large noncollinear heads, each with at least $c$ core sites. Each has at most $e+1$ labels. At most 2,000,025 labels lie off these three heads. [Extraction argument](three-head-residual-secant.md#reduction-to-three-saturated-heads) · [Logarithmic estimates](logarithmic-section-heights.md) · [Endpoint verifier](../../../scripts/probes/probe_three_head_successor_incidence.py)

Let $U$ be the complement of their three joint cores. Put $s=n-3c+2d$ and $\tau=t-3d$. The three-head determinant gives $|U|\le s$, and every outside witness agrees on at least $\tau$ sites of $U$. A failure requires at least $m=2n+1-3(e+1)$ outside labels. At the first row $s+3d<t$, excluding even one. In the other rows it suffices to take any $m$ outside labels. When $3\tau>2s+d$ every three agree together on more than $d$ sites, and polynomial uniqueness puts all on one affine head. [Secant theorem](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadResidualSecant.lean)

For the larger dimensions take $h=\lfloor m\tau/s\rfloor$, $p=\binom h2$ and $q=hp-\binom h3$. Let $w(x)$ count the selected outside witnesses agreeing on a site $x\in U$. Since $pw\le\binom w3+q$ for $0\le w\le m$, summation gives
$$
\sum_{x\in U}\binom{w(x)}3\ \ge\ pm\tau-sq\ >\ \binom m3d .
$$
Some triple agrees on more than $d$ such sites and hence defines one affine head $H_4$. If its joint core inside $U$ has size $J$, then $3\tau\le s+2J$. Away from the joint core of a line at most one of its labels can agree. Every point off that line agrees at no more than $d$ sites of this joint core. It would have $\tau+J\le s+d$, contradicting $5\tau>3s+2d$. Thus every outside point, including any that were not selected initially, is on $H_4$. For the seven largest dimensions the four-head incidence bound gives $c_4\le n+4d-3c$. The $m$ witnesses on that head require $mt\le n+(m-1)c_4$, which the integer test excludes. [Third-moment and endpoint checks](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadSuccessorIncidence.lean)

If $H_4$ is collinear over the function field with two old heads, take any two distinct outside labels on it. They agree together on at least $2\tau-s$ sites in $U$, all in its joint core. At each the two old heads have at most one distinct fresh scalar since their evaluated points and the received point are collinear. They have two off-core slots there. At every other site their old personal slot capacities are upper bounds. Hence the three old heads lose at least $2\tau-s$ slots. This exceeds the entire 2,000,025-label residual allowance. We may therefore take every triangle of the quartet to be nonzero.

## An inequality using the same sites for all four heads

At a site let $j\in\{0,1,2,3\}$ count old owners, $b\in\{0,1\}$ indicate fourth-head ownership, and $y$ count selected outside labels whose actual folds agree there. On the fourth core $y=m$, elsewhere $y\le1$. The four triangle root charges at total multiplicity zero through four are $F=(0,0,2,5,8)$. Summing the site counts gives
$$
\sum j\ge3c,\quad \sum y\ge mt,\quad
\sum (j-1)_+\le2d,\quad \sum jy\le3md,\quad \sum F(j+b)\le8d.
$$
The fourth inequality double-counts the agreements for each selected scalar on each old core. Its folded polynomial differs from that old head's fold and can share at most $d$ evaluation sites. For $m\ge3$ the finite site types satisfy
$$
4y+(4m-2)j\le4m+2(m-1)(j-1)_+ +2jy+(m-1)F(j+b).
$$
At $e=715,827,878$, $d=73,688,167$, summing this inequality for $m=12$ gives a contradiction by **198**. At $e=715,827,879$, $d=71,582,791$, the same bound excludes ten outside labels. Thus only nine could overrun at this second cell. Their three old heads must use all $3(e+1)=2n-8$ distinct personal labels, requiring a different finite label on every off-core slot. [Mixed incidence bound](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadSuccessorIncidence.lean)

For nine labels a second site inequality is
$$
17j+2y\le6(j+b)+12+8(j-1)_+ +jy+F(j+b).
$$
Consequently $6I_4\ge17I_3+18t-12n-51d$, with $I_3=\sum j$, $I_4=\sum(j+b)$. At the stated dimension the right side at $I_3=3c$ equals $6(n+4d)-3$. The integer upper bound $I_4\le n+4d$ forces $I_4=n+4d$ and $I_3=3c$. All sites have one or two owners. All four triangle budgets are exhausted, opposite edges have equal node counts and each head owns $2d$ doubles. Polynomial cancellation gives one fixed nonsingular involution pairing the projective directions of opposite sides, valid also at a coincidence of two heads. [Saturation and the opposite form](../../../ArkLib/Research/ProximityGap/Frontier/FourHeadCoreDeterminant.lean) · [Fresh-slot argument](eighth-saturated-opposite-directions.md)

The fourth core has size $c_4=286,331,156$. Nine outside labels need $9(t-c_4)=644,245,101$ distinct fresh positions. Only $3(c-2d)=644,245,086$ are singletons belonging to the old heads. Hence at least fifteen are doubles of two old heads. At such a double the fourth-head direction from the received point is paired with the direction of the one old head off its core: they are opposite edges, the shared endpoint values coming from the two owners. For each of the nine outside labels the involution permits at most one different old label in all these reserved slots. Fifteen occupied slots would need fifteen distinct labels. This excludes the last case.

The finite mixed inequalities, forced equality, third-moment selection, the common double interpolant and the seven larger endpoint tests are checked in Lean. The global factor estimates and their assembly with the site counts are written. Dimension monotonicity applies because the required agreement exceeds the largest dimension, and the line-to-interleaved equivalence supplies every positive width. [Lean proofs](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadSuccessorIncidence.lean) · [Dimension transfer](../../../ArkLib/Research/ProximityGap/Frontier/TerminalDimensionThreshold.lean)
