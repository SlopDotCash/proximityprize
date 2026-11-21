# The first named prime one error past the half-rate quarter radius

Put $n=2^{30}=4h$, $k=2h$, and $e=h+1=268435457$, so a witness needs $t=3h-1=805306367$ agreements. The first designated prime has budget $B=n$ at tolerance $2^{-128}$. The proved good count is $h$ and the first failure lies in $[268435457,313174699]$. Safety at $h+1$ would raise the left endpoint by one. The results here narrow the possible counterexamples. They do not establish safety for all received pairs. [Quarter-radius bound](../../../ArkLib/Research/ProximityGap/Frontier/ApolarHalfBreakpoint.lean) · [First-prime failure](../../../ArkLib/Research/ProximityGap/Frontier/FirstPrimeSepticCores.lean)

## What the present bounds give

Sharp apolarity requires both $k+d<n$ and $2e\le d+1$. With $k=2h$ the first inequality forces $d\le2h-1$, while $e=h+1$ requires $d\ge2h+1$. The corresponding weighted Johnson exception count also cannot certify this budget for any valid multiplicity, jet cutoff or height. Indeed its incidence ratio is $(n-D)/(t-D)=(2h+1)/h$, where $D=k-1$. The remaining parameters $b,H$ are at least one. Even the term $((n-D)/(t-D))(2D-1)H(2b-1)$ exceeds $n+1$. Lean verifies the obstruction for the implemented refined Johnson formula. A small ordinary list at each point on the received line does not alone bound the union of its bad scalars. [Apolar prerequisites](../../../ArkLib/Research/ProximityGap/Frontier/SharpApolarMCA.lean) · [Johnson and incidence results](../../../ArkLib/Research/ProximityGap/Frontier/FirstPrimeQuarterSuccessor.lean)

For fixed received rows $(u,v)$, call a pair of polynomials $(A_i,B_i)$ of degree $<k$ a head. Its joint core $C_i$ consists of the sites where it equals $(u,v)$. A decoding polynomial at scalar $z$ lies on this head when it equals $A_i+zB_i$. The following statements hold on every injective domain of the indicated length.

* **Four-word list cap.** Through 286331153 errors, the interleaved list of every center contains at most four words at every positive width.
* **Cover from four joint cores.** If four distinct heads each have at least $w=787410671$ joint sites, at every agreement threshold of at least $w$ all selected bad-scalar decoders lie on these heads.
* **Count at the successor.** If four determined secants have at least $w$ joint sites apiece, the total bad-scalar count at $e=h+1$ is at most $n+9$. A refined pair overlap limit of $k-2$ gives $n+3$ by the same formal inequality. The further restrictions below explain why $k-2$ is the relevant limit for a possible violation.

For the first two statements, consider five subsets of a domain of size $n$, each of cardinality at least $w$, with every pair intersecting in at most $d=k-1$. Counting memberships at each site and using $(j-3)(j-4)\ge0$ for its integer multiplicity $j$ yields $30w\le20d+12n$. The choice $w=\lfloor(20d+12n)/30\rfloor+1$ contradicts this. Five words in one ball would give five such agreement sets. For four joint cores and a decoder on none of their heads, use the four cores and that decoder's agreement set. Its intersection with each core contains at most $d$ points, by applying the polynomial root bound to the difference from that head at the given scalar. The core-core intersections obey the same bound. This proves coverage even if the projections of two heads coincide at the selected scalar. [Lean theorem and list predicate](../../../ArkLib/Research/ProximityGap/Frontier/FirstPrimeQuarterSuccessor.lean)

## What a four-head violation would require

Suppose the four heads cover more than $n$ distinct bad labels. If $L_i$ labels lie on head $i$, each needs a fresh agreement outside its own core: a witness contained entirely in that core would be jointly explained. At a site outside the core, at most one scalar agrees with that head. Hence
$$
L_i\max(1,t-|C_i|)\le n-|C_i|,\qquad L_i\le e+1=h+2.
$$
The four-head cover therefore forces $L_i\ge h-5$ for all $i$. A core smaller than $t-1$ would give $L_i\le(e+2)/2$ since $t-|C_i|\ge2$. Thus $|C_i|\ge t-1=3h-2$. In particular each head is determined by two of its selected labels.

Every triple of heads is collinear over $\mathbb F_p(X)$. Otherwise its determinant would have degree at most $2(k-1)$ and at least $\sum|C_i|-n\ge5h-6$ zeros with multiplicity: a site in two cores contributes one and a site in three contributes two. These inequalities are incompatible. Factor the difference of two heads into its polynomial content and a coprime direction $(P,Q)$. All four heads can then be written as one base pair plus $(P,Q)f_i$ with distinct polynomial $f_i$. This follows from collinearity and Bézout's identity for $P,Q$. Let $D_0=\max(\deg P,\deg Q)$. In each difference, $\deg(f_i-f_j)\le k-1-D_0$, so distinct core intersections are bounded by the same number. [Multiplicity argument](../../../ArkLib/Research/ProximityGap/Frontier/_HalfPredecessorRateQuarterDeterminantMultiplicity.lean) · [Primitive direction](../../../ArkLib/Research/ProximityGap/Frontier/_HalfPredecessorRateQuarterPrimitiveDirection.lean)

Write $U=\bigcup_i C_i$. With pair overlaps at most $b$, the same integer incidence estimate, now applied on $U$ with $(j-2)(j-3)\ge0$, gives
$$
16(3h-2)\le12b+6|U|.
$$
For $b=2h-1$ there are at most three uncovered sites. At a covered coordinate a fresh scalar from any head must satisfy $P(x)+zQ(x)=0$ since the received pair equals one of the heads there. Coprimality gives at most one such scalar per covered site. Uncovered sites supply at most four each. This gives $|U|+4(n-|U|)\le n+9$. A constant direction supplies at most one covered scalar in total, allowing at most 13 labels across the domain. Thus $D_0\ge1$. If $D_0\ge2$, then $12b+6n\le12(2h-3)+6n<16(3h-2)$. Consequently **$D_0=1$**. Taking $b=2h-2$ shows that at most one site is uncovered. An over-budget instance needs that site, since all-covered would give at most $n$ distinct labels.

For this last possible case let $a_j$ count sites appearing in exactly $j$ cores. Set $\Delta=\sum |C_i|-4(3h-2)\ge0$. The six pair intersections have total at most $6(2h-2)$. Subtracting twice the sum of the four core sizes and adding $3n$ gives
$$
3a_0+a_1+a_4\le4-2\Delta .
$$
With $a_0=1$, this forces $\Delta=0$, so **all four cores have size exactly $3h-2$**. Moreover $a_1+a_4\le1$. Counting memberships now gives $a_2=5-2a_1+a_4$. Only three occupancy profiles remain.

| Sites in one core | Sites in two cores | Sites in four cores | Maximum degree of the reduced cross-ratio |
|---:|---:|---:|---:|
| 0 | 5 | 0 | 2 |
| 1 | 3 | 0 | 1 |
| 0 | 6 | 1 | 2 |

To obtain the last column, take any two of the products $(f_1-f_2)(f_3-f_4)$, $(f_1-f_3)(f_2-f_4)$, $(f_1-f_4)(f_2-f_3)$. Each has degree at most $4h-4$. All three share one root per triple-core site and at least two per four-core site. Cancel these factors in the ratio of the first two products. Its numerator and denominator have degree at most $4h-4-a_3-2a_4$, as displayed. The ratio is nonconstant. At a two-core site, exactly the pair of matching heads shares the received value. One of the three products vanishes there and the other two do not. A constant ratio would make all three polynomials proportional by their alternating sum identity and would preclude that pattern.

The integer allocation probe constructs all three types at the actual length with each individual core and each of the six pair bounds satisfied. Thus these numerical inequalities cannot rule out an extra scalar. Showing that the required polynomial differences on the actual roots of unity exist or are impossible is a separate problem. There is also the complementary case in which fewer than four moderately large cores are available and the cover theorem supplies no classification of the remaining decoders. The cross-ratio reduction is a written argument. The linked Lean file checks the four-word cap, four-head coverage, conditional bad-scalar counts, the one-hole incidence inequality and the Johnson obstruction. [Occupancy probe](../../../scripts/probes/probe_quarter_successor_four_heads.py) · [Lean statements](../../../ArkLib/Research/ProximityGap/Frontier/FirstPrimeQuarterSuccessor.lean)

## Four-valued rational maps and the omitted head

In each of the three profiles, at least $4h-8$ sites belong to exactly three cores. Can the exceptional head at each such site be assigned using the four cosets of the index-four subgroup, with a few changes? Any such assignment would require at least **268435450 changes**. The following result allows unequal fiber sizes and a general four-valued rational function.

Let $X$ be an injective evaluation domain of size $n$, and let $f_0,\ldots,f_3$ be distinct polynomials of degree at most $d$ with $2d<n$. Suppose $G/B$ has height $r=\max(\deg G,\deg B)$, has no pole on $X$, and takes values in $\{a_0,a_1,a_2,a_3\}$ throughout $X$, with the $a_i$ distinct. At $x$, assign label $j$ when $G(x)/B(x)=a_j$. Call a site aligned when the other three heads all equal the received value $y(x)$. Then the number of aligned sites is **at most $r+d$**. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/FourFiberTripleAlignment.lean)

To prove this, relabel the fibers so that the union of fibers 2 and 3 contains more than $d$ points. This is possible since one of the complementary pairs contains at least $n/2$ sites. Define $E_i=(G-a_iB)f_i$. For each $j$ form
$$
H_j=(a_1-a_j)E_0+(a_j-a_0)E_1+(a_0-a_1)E_j.
$$
On an aligned site every $E_i(x)$ equals $(G(x)-a_iB(x))y(x)$, including the omitted head whose coefficient is zero. Thus $H_j$ vanishes there. If there were more than $r+d$ aligned sites, the degree bound would give $H_j=0$ identically. On fiber $j$, for $j=2,3$, this then gives
$$
 B(x)(a_j-a_0)(a_j-a_1)(f_0-f_1)(x)=0 .
$$
The first three factors are nonzero. The two fibers therefore supply more than $d$ roots of $f_0-f_1$, contradicting distinctness.

For the successor apply the theorem after subtracting one scalar head from all four, which preserves equality and gives $d=2h-2$ by the primitive-direction bound. A scalar received value $y(x)$ exists on each triple site because there the received pair equals the base pair plus $(P(x),Q(x))f_i(x)$ for each matching head, and coprimality makes $(P(x),Q(x))$ nonzero. Extend $y$ arbitrarily elsewhere. On a triple site exactly one head differs, so alignment precisely tests the prescribed omitted label. A classifier of height $r\le h$ can match at most $3h-2$ of the $4h-8$ or more triple sites. The mismatch count is at least $h-6=268435450$. In particular this applies to $G/B=X^h$ on the order-$4h$ subgroup under every labeling of its four values. Exact matching by any four-valued rational map on the whole domain would require height at least $2h-6=536870906$. This argument leaves arbitrary assignments of the omitted labels open.

A small sharp example is the order-eight subgroup of $\mathbb F_{17}^{\times}$ with $G/B=X^2$ and $d=2$. Choose $p_0,p_1,p_2,p_3=1,2,4,8$, one from each square fiber, and set $y(x)=x^3$. The distinct quadratics $f_i(X)=X^3-\prod_{j\ne i}(X-p_j)$ give exactly the prescribed three matches at every $p_i$. Thus four aligned sites attain $r+d=4$. [Finite-field check](../../../scripts/probes/probe_quarter_successor_four_heads.py)
