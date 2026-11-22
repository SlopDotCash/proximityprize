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

## Split polynomials with a common remainder

This section restates the profile with one single-core site and three two-core sites as a statement about four vanishing polynomials, shows that any realization is over budget, and records exhaustive searches at small lengths for that profile and for all four-head families. It does not decide the production case.

**Structure.** All six pair overlaps sum to $12h-12=6(2h-2)$, so every difference $f_a-f_b$ has degree exactly $2h-2$ and its roots are exactly $C_a\cap C_b$. Each perfect matching of the heads carries one two-core site. A star of three pairs through one head would force $2|S|=2h-3$ for the three other omitted classes, so the three two-core pairs form a triangle. Number the heads so that the triangle is $\{0,1,2\}$, let $S_i$ be the triple sites that omit head $i$, and let $v_i$ be the monic polynomial vanishing on $S_i$. Then $|S_0|=|S_1|=|S_2|=h-1$, $|S_3|=h-2$, the single-core site lies in $C_3$, and
$$
f_0-f_3=\lambda_{03}v_1v_2,\qquad f_1-f_3=\lambda_{13}v_0v_2,\qquad f_2-f_3=\lambda_{23}v_0v_1 .
$$
Subtracting these in pairs and cancelling the common factor gives, with the two-core sites $r_{01},r_{02},r_{12}$,
$$
\lambda_{03}v_1-\lambda_{13}v_0=\lambda_{01}(X-r_{01})v_3,\quad
\lambda_{03}v_2-\lambda_{23}v_0=\lambda_{02}(X-r_{02})v_3,\quad
\lambda_{13}v_2-\lambda_{23}v_1=\lambda_{12}(X-r_{12})v_3 .
$$
So $v_0,v_1,v_2$ are proportional on $S_3$: up to scalars they have **one common remainder modulo $v_3$**. Equivalently $v_0/v_3$ agrees with three linear functions on $S_0$, $S_1$ and $S_2$, and the three lines meet pairwise above the sites $r_{01},r_{02},r_{12}$.

**Converse.** Suppose pairwise disjoint sets $S_0,S_1,S_2$ of size $h-1$ and $S_3$ of size $h-2$ in a domain of size $4h$ satisfy the three relations with nonzero constants and three distinct further sites $r_{ab}$. Put $f_3=0$ and define $f_0,f_1,f_2$ by the first display. Let $y$ be zero on $S_0\cup S_1\cup S_2$ and on one of the two remaining sites, the common value of $f_0,f_1,f_2$ on $S_3$, and $f_a=f_b$ at $r_{ab}$. Each core then has exactly $3h-2$ sites and one site is uncovered. With a coprime linear direction $(P,Q)$ having no root on the domain, the heads $(Pf_i,Qf_i)$ have degree below $2h$. At a covered site $x$ outside the core of head $i$ the scalar $z(x)=-P(x)/Q(x)$ makes that head agree on its core and on $x$, which is $3h-1$ sites, and the pair is not jointly explained there. The map $x\mapsto z(x)$ is injective, so the covered sites give $4h-1$ distinct bad scalars. The received values at the uncovered site can be chosen so that the four heads contribute four further scalars. The total is $4h+3$. **A realization on the first designated domain would therefore fix the first failure at 268435457.**

**The concurrent case stays within budget.** If the three sites $r_{ab}$ coincide, the four polynomials $v_0,v_1,v_2,(X-r)v_3$ lie in one pencil and vanish on four disjoint fibers of size $h-1$. Each of the four remaining sites can join only one core, because the four heads take pairwise distinct values there. Giving one remaining site to each core covers every site, and these heads then have exactly $4h$ bad scalars, which equals the budget. One family of such pencils needs $h-1=2m$ with $m$ dividing $4h$: the map $x^m+c\,x^{-m}$ has fibers of size $2m$ inside the group of $4h$-th roots of unity. This forces $h\in\{3,5,9\}$. For $h$ a power of two the degree $h-1$ is odd and coprime to $4h$, so no power map can be a factor.

**Search for this profile.** For $h=4,5,6,7$ and a prime just below $2^{31}$, every choice of $S_3$ and $S_0$ up to rotation was examined for further split members of the span of $v_0$, $v_3$ and $Xv_3$.

| $h$ | Sites | Pairs $(S_3,S_0)$ | With a further split member | With two on disjoint sets | Configurations |
|---:|---:|---:|---:|---:|---:|
| 4 | 16 | 5460 | 1348 | 152 | 0 |
| 5 | 20 | 406980 | 1272 | 108 | 0 |
| 6 | 24 | 27457584 | 80 | 0 | 0 |
| 7 | 28 | 1771619850 | 270 | 0 | 0 |

At $h=5$ the 108 cases are the pencils $x^2+c\,x^{-2}$ with coincident sites. At $h=4$ the counts are the same at a second prime. No case has three distinct two-core sites on the domain.

Small fields behave differently. At $h=4$ the field $\mathbb F_{17}$ has 4104 configurations and the thirteen primes from 97 to 641 have none. At $h=5$ the field $\mathbb F_{41}$ has nine and the thirteen primes from 61 to 661 have none. Exhaustive decoding of one $\mathbb F_{41}$ configuration finds **23 bad scalars on 20 sites**, which is $4h+3$ and confirms the converse numerically. [Search program](../../../scripts/probes/probe_successor_common_remainder.cpp) · [Exhaustive check over $\mathbb F_{41}$](../../../scripts/probes/probe_successor_converse_check.py)

**Search over all four-head families.** A second program does not assume a profile. It uses only that an over-budget family has four cores of size $3h-2$ beside an uncovered site, and that at most one of the six differences has fewer than $2h-2$ roots on the domain. Number the heads so that a short difference, if any, is $f_0-f_1$, and subtract $f_3$. Then $f_0=V_{Z_0}$, $f_1=\lambda_1V_{Z_1}$ and $f_2=\lambda_2V_{Z_2}$ for three site sets of size $2h-2$. The program enumerates the sets, takes the constants from repeated ratio values, and for each family chooses the received row by a dynamic programme that maximises the bad scalars with all four cores of size $3h-2$.

| $h$ | Prime | Families | Admitting an uncovered site | Largest count | Over budget |
|---:|---:|---:|---:|---:|---:|
| 4 | 2147483489 | 15502872 | 2880 | 16 | 0 |
| 5 | 2147482921 | 236400 | 0 | none | 0 |
| 4 | 97 | 26875824 | 4080 | 19 | 48 |
| 4 | 337 | 16093128 | 3456 | 19 | 288 |
| 4 | 113, 193, 241, 257, 449, 641 | 15512712 to 23164848 | 2880 to 4176 | 16 | 0 |

A family is listed once for every admissible numbering of its heads, so these are not orbit counts. Exhaustive decoding of one $\mathbb F_{97}$ family finds **19 bad scalars on 16 sites**, the predicted count. At 16 sites the budget itself is attained over every prime tested. Over-budget four-head families therefore occur over isolated small primes, here 97 and 337 at 16 sites and 41 at 20 sites, and over no large prime tested.

These are finite checks at 16 and 20 sites, and up to 28 sites for the first profile. They are evidence that four heads do not exceed the budget one error past the quarter radius over a large prime. They are not a proof at the production length. Even if no family exists there in characteristic zero, families can occur over the finitely many primes dividing certain obstruction norms, as at 97, 337 and 41 above, and those norms are far too large to compare with the designated prime. Received pairs without four large cores are not covered. [All-profile search](../../../scripts/probes/probe_successor_four_head_census.cpp) · [Exhaustive decoding of a reported family](../../../scripts/probes/probe_successor_family_decode.py)
