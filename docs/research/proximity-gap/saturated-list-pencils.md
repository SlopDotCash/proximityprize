# Fully split differences at the production Johnson boundary

Let $n=2^{30}$, $k=n/8$, $D=k-1$, and $t=379625061$. The two nominated field budgets are $n$ and $2n$. Take $M$ distinct scalar Reed–Solomon words of dimension $k$ agreeing with one center on at least $t$ sites each. Choose an arbitrary subset $S_i$ of exactly $t$ sites from each agreement set. Two selected sets meet in at most $D$ sites. Call a pair saturated when its intersection has $D$ elements. Its polynomial difference then has degree $D$ and its roots are precisely those $D$ distinct evaluation points.

## What an oversized list forces

Put $C=\binom M2$ and write $Mt=nq+r$, $0\le r<n$. Counting intersections at each site and balancing the integer point degrees gives
\[
\sum_{i<j}|S_i\cap S_j|\ge(n-r)\binom q2+r\binom{q+1}2.
\]
Every unsaturated pair contributes at most $D-1$. Subtracting $(D-1)C$ gives these lower bounds on the number of saturated pairs. Turán's theorem gives the indicated complete subgraphs.

| Selected list size | Saturated pairs, at least | Fraction of all pairs | Forced clique |
| --- | ---: | ---: | ---: |
| $n+1$ | 410,960,812,476,257,241 | 71.29% | 4 |
| $2n+1$ | 1,907,347,367,389,145,010 | 82.71% | 6 |

The bound also carries information across groups of words. If a simple graph on $M$ vertices has $E$ edges, some $a$ vertices have at least $\lfloor M\binom{\lfloor2E/M\rfloor}{a}/\binom Ma\rfloor$ common neighbors. Sum $\binom{\deg v}a$ over the vertices and balance the degrees. For the first row, some 48 words have at least 94 common neighbors, all of whose cross differences are saturated. All these statements apply to **every** selection of $t$ agreement sites per word. [Formal intersection and clique bounds](../../../ArkLib/Research/ProximityGap/Frontier/SaturatedListCliques.lean)

A saturated four-clique forces three disjoint full fibers of a nonconstant rational function even after removing common roots. Let $n_j$ count sites lying in exactly $j$ of its four selected sets. Six pair intersections of size $D$ give $6D=\sum_j\binom j2n_j$. Since $\sum_j jn_j=4t$, subtracting overlaps in the union gives $n_3+3n_4\le n+6D-4t$. The four triple intersections sum to $n_3+4n_4\le4(n_3+3n_4)/3$. Some triple therefore has common root count $c\le(n+6D-4t)/3$. For messages $f,g,h$ of this triple take the ratio $(f-h)/(g-h)$ and cancel the monic common-root polynomial. The fibers above $0,1,\infty$ are disjoint sets of precisely $D-c$ distinct domain points. Their common size is at least **14,035,080**. All roots of each difference already lie in its selected pair intersection, which justifies the exact common-root degree in this argument.

## Six actual fully split words on every smooth domain

In fact large full fibers and an actual six-clique occur on all the smooth domains under discussion. Write the domain as $a\mu_n$, put $d=n/16$, and set $Y=(X/a)^d$. Fix a primitive sixteenth root $z$. Each $Y=z^j$ has exactly $d$ simple roots on the domain. Take the following six points $(u_i,v_i)$ in a coefficient plane. The first two are $(0,0)$ and $(1,1)$. For each of $(r,s)=(1,2),(3,4),(7,9),(8,9)$ take the intersection of $v=z^r u$ and $v-1=z^s(u-1)$. Its coordinates are $u=(1-z^s)/(z^r-z^s)$ and $v=z^r u$.

The exponent of $(v_i-v_j)/(u_i-u_j)$ for $i<j$, in lexicographic pair order, is
\[
0,1,3,7,8,\quad 2,4,9,9,\quad 5,11,10,\quad 15,12,\quad 9.
\]
The three nines correspond to the single triple $\{1,4,5\}$. Each other exponent occurs once. The accompanying certificate computes in $\mathbb Z[Z]/(Z^8+1)$. The denominators and nonzero abscissa differences in homogeneous coordinates have norms that are powers of two. These identities therefore specialize to every field containing a primitive sixteenth root in odd characteristic. [Exact cyclotomic certificate](../../../scripts/probes/probe_six_split_list.py)

Choose $d-1$ sites outside the thirteen used fibers, and let $P$ be their monic vanisher. Take the six messages $P(X)(v_i-u_iY)$. Every difference has exactly $(d-1)+d=D$ simple domain roots. Set the center to zero on the common roots and to each tied pair's value on its whole fiber. All three heads of the repeated fiber give the same value. The numbers of incident fibers for the six words are $5,4,5,5,4,4$. The remaining $2d+1$ sites suffice to bring all three shorter words to **380,283,562** agreements by dividing them equally. The other three already have $6d-1$ agreements. Thus six distinct codewords lie in the same ball even at 693,458,262 errors. At the stated $t$ there are 1,975,503 spare sites. The messages, center, exact pairwise overlap, and lower bound for the canonical worst-center list are verified for every supplied smooth domain. [Kernel-checked smooth witness](../../../ArkLib/Research/ProximityGap/Frontier/SixSplitListWitness.lean)

For any four or five of the five heads $P(X)(b_iY+b_i^{-1})$, where $b_i=z^{e_i}$ and $e_i\in\{0,1,2,4,7\}$, all unordered two-term exponents are distinct modulo sixteen. Choose the common vanisher of degree $d-1$ outside these ten fibers. Its roots and the four incident fibers give every word $5d-1$ mandatory sites. Disjoint additional sites raise every word to exactly $t$ chosen agreements since the free supply is $5d+1$ and each deficit is $t-5d+1$. This example preserves all ten pair intersections **after** choosing exactly $t$ sites per word. In contrast, three of the six heads from the previous construction have $6d-1>t$ mandatory sites. Its full six-clique is a statement about actual agreement sets. Lean verifies the cropped five-clique throughout the full integer interval from $5d-1$ through $6d-1$ for every smooth coset of size $16d$. [Kernel-checked exact supports](../../../ArkLib/Research/ProximityGap/Frontier/FiveCroppedSplitPencil.lean)

## Lists with common evaluation sites

Fix $s$ sites and prescribe the same column of width $w$ to every candidate
at each of them. A center can take arbitrary values there. If each candidate
agrees with the center at $t>s$ sites, deleting the prescribed sites leaves
at least $t-s$ agreements per candidate. Since distinct dimension-$k$
Reed–Solomon words agree in at most $k-1$ columns and already agree at all
$s$ sites, the remaining pairwise overlap is at most $k-1-s$ when $s<k$.
The strict Johnson rank bound on the remaining coordinates gives at most
$n-s$ candidates as soon as
\[
 (t-s)^2>(n-s)(k-1-s).
\]
This also applies to every family constructed by adding a common word to
polynomials all divisible by the same split vanishing factor.

At length $n=2^{30}$ the first prime's budget is $n$. Each row gives a
certified safe error count **within the prescribed evaluation slice**.

| Prescribed sites | Rate $1/8$ | Rate $1/16$ | Upper bound on the slice list |
|---:|---:|---:|---:|
| 1 | 694,116,763 | 805,306,371 | 1,073,741,823 |
| $2^{23}-1$ | 699,221,467 | 815,237,616 | 1,065,353,217 |
| $2^{26}-1$ | 746,721,448 | | 1,006,632,961 |

Thus a list exceeding the first budget at either next open Hamming step
must vary at every site. The five cropped power-fiber witnesses above share
a factor with $2^{26}-1$ roots. Even adding arbitrary new messages with the
same values at these sites keeps their rate-$1/8$ list under budget through
746,721,448 errors. This conclusion allows every center and every interleaving
width. Independent verified kernel replay accepted 28,288 declarations for the general theorem and all three numerical specializations. The unrestricted first failing counts remain open. [Affine-slice
list theorem and numerical bounds](../../../ArkLib/Research/ProximityGap/Frontier/SharedSiteListBound.lean)

## What a low-dimensional list can contribute

An affine line of messages contains at most $\lfloor(n-D)/(t-D)\rfloor=3$ members of the list. Its direction vanishes on at most $D$ sites. Each other site agrees with at most one member. More generally let $A$ be an affine $r$-flat of message polynomials. The coordinate evaluations that are constant on $A$ number at most $k-r$. The independent $r$-dimensional direction space consists of polynomials sharing all these roots, and division by their vanisher embeds it in the space of polynomials of degree below $k-c$. At a nonconstant coordinate the received value cuts $A$ in an affine $(r-1)$-flat. Counting agreements gives the recursive upper bound
\[
L_0=1,\qquad L_r=\left\lfloor L_{r-1}\frac{n-k+r}{t-k+r}\right\rfloor.
\]
Indeed for $c$ constant coordinates one has $M(t-c)\le L_{r-1}(n-c)$, and the quotient $(n-c)/(t-c)$ increases with $c$. The first two upper bounds are 3 and 11. At affine dimensions 15, 16, and 17 the bounds are 413,761,349, 1,584,055,105, and 6,064,439,257. A list above the first nominated budget requires affine dimension at least 16. The local split examples leave open the simultaneous constraints among a family of that dimension. The punctured Johnson theorem already bounds the second nominated prime at this step. [Punctured list cap](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListJohnsonPuncture.lean)

## Classification for a common locator and a single power

Consider six polynomials $P(X)(u_iX^m+v_i)$ of degree at most $D$ on a smooth coset of size $n$. Suppose every pair of selected agreement sets, each of size exactly $t$, meets in $D$ sites. Then $P$ has degree $c=D-m$ and $c$ simple roots on the domain. All secants have nonvertical direction. Each pair's remaining $m$ zeros must form one full power fiber, disjoint from the roots of $P$. A nonempty power fiber on a cyclic coset has size $\gcd(n,m)$, so $m\mid n$. Counting the six individual agreements charges at most $n$ sites once, at most $5c$ more at common roots, and at most $15m$ remaining pair incidences. Thus $6t\le n+5D+10m$. At these parameters the inequality forces $m>n/32$, while $m\le D<n/8$; the only possible divisor is $m=n/16$.

Represent each head by its coefficient point; signs and the coset scale can be absorbed in one axis. Its secants must then have slopes in $\mu_{16}$. Two parallel secant lines with distinct intercepts cannot both occur: their pairs would require different center values on the same entire power fiber. Normalize two points to $(0,0)$ and $(1,1)$ by translation and independent rescaling of the two axes. This divides all secant slopes by the original pair's slope and hence preserves the allowed root set. Six collinear points would require $6t\le n+5D$, which fails, so there is a third point off the diagonal. Such a point is determined by two distinct slopes in $\mu_{16}\setminus\{1\}$ from the first two points. There are 210 options. After fixing one such third point, every additional diagonal point is determined by its slope to that point. This leaves a finite exhaustive tree over each designated prime field.

For a compatible configuration let $R$ be its total number of secant slopes and $r_i$ the number of their lines through head $i$. Each word must retain all $c+r_i m$ mandatory sites. The unused pool has $n-c-Rm$ sites, with at most one additional agreement per site. A compatible center and cropped supports therefore exist exactly when every $c+r_i m\le t$ and the summed deficits fit in the unused pool. At each nominated prime the exact enumerator visits 122,430 compatible normalized six-point configurations. All fail this test. Thus a cropped saturated $K_6$ excludes this entire ansatz at these two primes. The surviving $K_4$ and $K_5$ constructions describe the obstruction at the first budget, and the second budget already has a punctured Johnson upper bound. [Exact field enumeration](../../../scripts/probes/probe_six_split_power_class.py)

## First step beyond the half-rate Johnson floor

At length $n=2^{30}$, dimension $k=n/2$, and **314,491,700 errors**, every scalar list of more than $n$ words has four distinct messages whose six pairwise differences split over the ground field. Each pair agrees with the center at at least 536,870,910 distinct common positions. This holds on every injective domain. For the two named primes the scalar projection criterion transfers the obstruction to lists exceeding their respective budgets at any positive interleaving width. [Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/HalfListSplitDifferences.lean) · [Scalar projection](interleaved-list-projection.md)

Write $t=759250124$ for the required agreements, $D=k-1$ for the degree cap and $M=n+1$. Choose exactly $t$ agreement positions per message. Balancing the integer number of chosen words at each site gives a lower bound on the total pair intersections. Pairs meeting in fewer than $D-1$ positions contribute at most $D-2$, while every pair contributes at most $D$. The number meeting in at least $D-1$ positions is therefore at least **399,818,008,492,777,800**. A graph on $M$ vertices without a four-clique has at most **384,307,168,918,110,208** edges. For each edge of the resulting clique, divide the polynomial difference by the product of its known linear factors. The quotient has degree at most one, which proves splitting even if its last root lies outside the evaluation domain.

The four messages must also be affinely independent. To see this, suppose a minimal affine relation uses $m\in\{2,3,4\}$ of them. At any evaluation point, exactly $m-1$ messages cannot agree with the center, since the last coefficient is nonzero and the coefficients sum to zero. If $s$ messages agree there, then $(s-(m-2))(s-m)\ge 0$. Sum this inequality over the sites and use the bound of $D$ on each pair intersection. It gives $(2m-3)t\le (m-2)n+$m-1$D$. The displayed parameters violate this inequality for each of the three values of $m$. Thus any example would require at least three independent polynomial differences. This argument concerns affine dimension and leaves open whether such a list exists. The certified half-rate safe floor is still 314,491,699 errors.

## Disjoint groups in the same received list

An over-budget list must continue to contain split differences after many of its messages are removed. The following counts hold on any injective evaluation domain at the specified length. At each of the two nominated primes, overflow at any positive interleaving width implies scalar overflow at the same radius. All the groups in a row then belong to one scalar list around one received word. [Packing and named-prime proofs](../../../ArkLib/Research/ProximityGap/Frontier/RobustSplitListCliques.lean)

| Budget | Rate | Errors | Disjoint groups | Messages per group | Common domain roots per pair, at least |
|---:|---:|---:|---:|---:|---:|
| $2^{30}$ | $1/2$ | 314,491,700 | 55,363,904 | 4 | 536,870,910 |
| $2^{30}$ | $1/8$ | 694,116,763 | 25,809,976 | 7 | 134,217,726 |
| $2^{31}$ | $1/8$ | 694,116,764 | 366,766,857 | 3 | 134,217,726 |

For example, in the first-prime eighth-rate row, take any 893,071,997 remaining messages. The integer pair-incidence estimate with tangent parameter 315,748,631 gives more edges than any graph on this many vertices without a seven-clique. Two messages form an edge when they agree with the received word on at least 134,217,726 common selected coordinates. Their difference has degree at most 134,217,727. Dividing out the known roots leaves a polynomial of degree at most one, so the entire difference splits over the field. Remove those seven messages and reapply the same estimate while enough remain. These necessary configurations leave the named list endpoints open.

## Testing the two end coefficients

On a smooth coset where every site satisfies $(-x)^n=c$, a nonzero polynomial of degree at most $d$ with $d$ distinct physical roots has leading coefficient $L\ne0$ and constant coefficient $A$ satisfying $A^n=L^n c^d$. Indeed, $A/L$ is the product of the negatives of the roots. Applying this identity to message differences gives an executable necessary edge count using only two coefficients per message. For a subgroup of order $n$ coprime to $d$, every subgroup element occurs as a product of $d$ distinct sites, by rotating a fixed subset.

For a family whose message coefficients satisfy $A=uL+b$ with $u^n\ne c^d$, distinct messages have at most $d-1$ common domain evaluations. The strict Johnson rank bound therefore limits every interleaved list in this subcode to $n$ whenever $t^2>n(d-1)$, for arbitrary received words. The first open agreement count at each named budget and rate meets this inequality. Deciding the full code still requires control of messages across different affine slices. [Coefficient test and interleaved bound](../../../ArkLib/Research/ProximityGap/Frontier/SplitCoefficientSecants.lean)
