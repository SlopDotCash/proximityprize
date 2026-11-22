# Exact list-decoding thresholds on smooth Reed–Solomon domains

For the tolerance $2^{-128}$ the following Reed–Solomon codes have exact closed-ball thresholds. Both statements hold at every positive interleaving width. The first bad Hamming count is the first error count for which some received word has more than $B=\lfloor |F|/2^{128}\rfloor$ nearby codewords.

| Alphabet and evaluation domain | Length | Dimension | Last good errors | First bad errors | Supremum of good radii |
|---|---:|---:|---:|---:|---:|
| BLS12-381 scalar field, order-256 subgroup | 256 | 32 | 222 | 223 | $223/256$ |
| $\mathbb F_{257^{27}}$, order-128 subgroup of $\mathbb F_{257}^\times$ | 128 | 32 | 93 | 94 | $47/64$ |

At either endpoint the closed-ball test fails. On the Hamming grid the maximum good radius is the last-good count divided by the length. Each endpoint lies strictly between its code's Johnson radius and the sponsor's capacity radius $(n-k+1)/n$. These are two parameter instances of the sponsor's grand list-decoding challenge. [Grand challenge](https://proximityprize.org/) · [Arnon–Boneh–Fenzi](https://eprint.iacr.org/2026/680) · [BLS scalar field](https://github.com/ethereum/annotated-spec/blob/master/deneb/polynomial-commitments.md)

## Complete four-rate examples

The same argument gives the following first bad error counts at tolerance $2^{-128}$. In each row the alphabet and domain stay fixed across all four rates. Divide by the length for the real supremum. The budget holds at every smaller radius, for every positive interleaving width.

| Alphabet and subgroup order | Rate $1/2$ | Rate $1/4$ | Rate $1/8$ | Rate $1/16$ |
|---|---:|---:|---:|---:|
| $\mathbb F_p$ with $p=65\cdot 2^{239}+1$, order 128 | 63 | 97 | 113 | 121 |
| $\mathbb F_{641^{26}}$, order 128 | 63 | 97 | 113 | 121 |
| $\mathbb F_{673^{16}}$, order 32 | 15 | 24 | 29 | 31 |

For the order-128 domains the result holds throughout the field-size interval where $\lfloor\binom{128}{64}/\binom{66}{64}\rfloor\le B$ and $128B<\binom{128}{65}$. The 246-bit prime $p=65\cdot2^{239}+1$ has Lucas witness 3 and budget $168749647902381897927241130699653120$. At rate one half, the fixed-product construction produces the first failure strictly between Johnson and capacity for each domain. The length-32 quarter-rate case first fails at 24 errors, one below the capacity count of 25. A monic center $X^k$ has a distinct candidate $X^k-L_T$ for every $k$-subset $T$, where $L_T$ is its monic locator. At the eight other endpoints, packing is safe at $k$ agreements. At $k-1$ agreements the ball about zero contains every scalar multiple of a locator with $k-1$ roots, exceeding the prize budget. These eight first failures occur at the capacity count $n-k+1$.

The kernel-verified statements include the radius at every rate and the repository's full `listDecodingPrize` predicate for each field. [Prime-field theorem](../../../ArkLib/Research/ProximityGap/Frontier/FourRateListPrime246.lean) · [General order-128 theorem](../../../ArkLib/Research/ProximityGap/Frontier/FourRateList128.lean) · [Extension-field length-128 theorem](../../../ArkLib/Research/ProximityGap/Frontier/FourRateList641.lean) · [Length-32 theorem](../../../ArkLib/Research/ProximityGap/Frontier/FourRateList673.lean)

## The upper bound on list size

Take any received word with any number of rows. Among the $n$ evaluation points, each list member with at least $t$ joint agreements has at least $\binom tk$ subsets of size $k$ on which every row agrees. No two distinct list members can claim the same subset, because $k$ common interpolation values determine each polynomial of degree below $k$. Thus every such list has size at most $\lfloor\binom nk/\binom tk\rfloor$.

## Integer packing and a four-rate threshold interval

For $k\le t$ and $2t\le n+k$, the maximum list at $t$ agreements is at most
\[
\min\{J(n,t,k),J(n,n-t,n+k-2t)\},\qquad
J(n,t,0)=1,\quad J(n,t,k+1)=\left\lfloor\frac{n J(n-1,t-1,k)}{t}\right\rfloor.
\]
Choose exactly $t$ agreement coordinates for each candidate. Distinct chosen sets intersect in fewer than $k$ coordinates, since agreement on $k$ sites determines every row. The sets containing a given coordinate satisfy the same condition after it is removed, with each of the three parameters one smaller. Summing the resulting bound over all $n$ coordinates counts each chosen set $t$ times. The complementary $(n-t)$-sets have intersections smaller than $n+k-2t$, giving the second bound. This is the Johnson–Schönheim recursion applied to a constant-weight binary code and its complements. It applies directly to every supplied injective domain and every positive interleaving width. [Johnson’s packing bound](https://doi.org/10.1109/TIT.1962.1057714) · [Lean proof and threshold theorem](../../../ArkLib/Research/ProximityGap/Frontier/RecursiveListPacking.lean)

At $t=k+1$, whenever the smaller recursive bound is at most $B<\binom nk$, the first failing error count is exactly $n-k$. At $k$ agreements the monomial center attains $\binom nk$ codewords. For example, at $(n,k,t)=(128,64,65)$ the complementary recursion gives **351980102567944271741142966174134400**, below the direct recursion's 362809707601132265209624858889168317 and the unrounded binomial bound 368479169875816659479009042713546950.

At every field size $q$ with $351980102567944271741142966174134400\le\lfloor q/2^{128}\rfloor<\binom{128}{64}$, the four first failures are **64, 97, 113, 121** errors, in decreasing rate order, on every supplied 128-point evaluation domain. The prime $p=2219\cdot2^{235}+1$ lies in the part of this interval added by the complementary recursion. Its budget is 360053335284024453365911604829356032. Lean checks its Lucas primality certificate, an element of order 128, and the closed-ball inequalities at every real radius. [Arithmetic and four-rate theorem](../../../ArkLib/Research/ProximityGap/Frontier/RecursiveListPacking.lean)

## A lower bound for a multiplicative domain

Let $D$ have $n$ distinct evaluation points in a subgroup $H\subset K^\times$ of order $h$, where $K$ is a finite field of order $q_0$ inside the code alphabet $F$. Choose $a\ge0$ and put $t=k+1+a\le n$. For each $t$-subset $T\subset D$, form its monic locator $L_T(X)=\prod_{x\in T}(X-x)$. Group subsets by their product in $H$ and by the $a$ coefficients of $X^{k+1},\ldots,X^{k+a}$ in $L_T$. There are at most $h q_0^a$ groups. Fix a largest group and use one of its locators $P$ to define a single received word $w(x)=P(x)/x$.

For each member $T$ of that group put $f_T=(P-L_T)/X$. The numerator has zero constant term because the products and cardinalities agree. Its degree is at most $k$, since the locators are monic of degree $t$ and have equal coefficients down through degree $k+1$. Thus $f_T$ is a polynomial of degree below $k$. Its agreements with $w$ are exactly the points of $T$, since $x\ne0$ and $w(x)-f_T(x)=L_T(x)/x$. Distinct subsets give distinct codewords. Extension of the alphabet preserves all their agreements and distinctions. Repeating the scalar row in all components gives the same lower bound at any positive width. Consequently some list at $t$ agreements has size at least
$$
\left\lceil\frac{\binom nt}{h q_0^a}\right\rceil .
$$

For $a=0$, prescribing the product is the quotient construction of Al Kindi, Proposition 2.1. The second instance uses the product and one more coefficient over the smaller field. Applying the upper bound at $t+1$ and the lower bound at $t$ locates the first failing Hamming step whenever the budget falls between them. [Al Kindi, Proposition 2.1](https://eprint.iacr.org/2026/2245)

## Integer certificates

| $(n,k,t)$ | Maximum allowed list $B$ | Upper bound at $t+1$ agreements | Lower bound at $t$ agreements |
|---|---:|---:|---:|
| $(256,32,33)$ | 154095187621958656428822154526901524485 | 103822805756204557481443916015906283000 | 1544364235623542792536478250736605959625 |
| $(128,32,34)$ | 343838801976411190589077691 | 225791737433503539600072540 | 365154439185991862436887742 |

The BLS12-381 scalar prime has an element of order 256. In the second case the multiplicative group of the prime field has order 256, hence a subgroup of order 128, and the extension field has order $257^{27}<2^{256}$. For both cases the displayed upper bound is at most the integer budget and the displayed lower bound is strictly greater. Since distances are multiples of $1/n$, these checks cover every real radius.

The general Lean lemmas are in [AgreementSubsetListPacking](../../../ArkLib/Research/ProximityGap/Frontier/AgreementSubsetListPacking.lean), [PrescribedProductList](../../../ArkLib/Research/ProximityGap/Frontier/PrescribedProductList.lean), and [ListScalarExtension](../../../ArkLib/Research/ProximityGap/Frontier/ListScalarExtension.lean). The exact arithmetic and a small explicit polynomial reconstruction can be reproduced with [the probe](../../../scripts/probes/probe_prescribed_product_list_thresholds.py).

## Formal statements

The uniform [budget-window theorem](../../../ArkLib/Research/ProximityGap/Frontier/PrescribedProductThreshold.lean) proves the exact cutoff for any positive width whenever the two displayed counting bounds straddle the budget. The [BLS12-381 theorem](../../../ArkLib/Research/ProximityGap/Frontier/BlsScalarListThreshold.lean) and [degree-27 extension theorem](../../../ArkLib/Research/ProximityGap/Frontier/SubfieldQuarterListThreshold.lean) instantiate the sponsor's unrounded tolerance. The BLS theorem also proves that the first failure at dimension 16 is 241 errors, by the minimum-distance argument.

## Uniform bounds at larger smooth lengths

Let $h$ be the minimum length in the table below, let $j=hR$ for the stated rate $R$, and write $n=mh$. On every smooth domain over $q<2^{256}$, the first failing Hamming count at tolerance $2^{-128}$ is at most $(h-j-2)m+1$ for every positive interleaving width. The strict comparison uses the actual unrounded sponsor budget. [Four-rate bounds and first-failure theorem](../../../ArkLib/Research/ProximityGap/SmoothReservedListBoundary.lean)

| Rate | Base $h$ | First failing errors at most | Uniform failing radius for $n>h$ |
|---|---:|---:|---:|
| $1/2$ | 256 | $126m+1$ | $253/512$ |
| $1/4$ | 256 | $190m+1$ | $381/512$ |
| $1/8$ | 256 | $222m+1$ | $445/512$ |
| $1/16$ | 512 | $478m+1$ | $957/1024$ |

To see why the bound improves with length, reserve one of the $h$ values of the power map $x\mapsto x^m$. On the remaining $h-1$ values, the prescribed-product count gives a list larger than the budget at $j+1$ agreements. Compose each candidate polynomial with the power map. Its degree is at most $(j-1)m$, leaving room to multiply both the candidate and the received word by a common locator of degree $m-1$. Put those roots at all but one site of the reserved fiber. Every candidate then has at least $(j+1)m+(m-1)$ agreements. The argument is Al Kindi’s finite construction. Lean also proves the lift for arbitrary regular projections defined by a degree-$m$ polynomial and for arbitrary punctured base lists. [Al Kindi, Theorem 1.1](https://eprint.iacr.org/2026/2245) · [Lean lift](../../../ArkLib/Research/ProximityGap/Frontier/SmoothReservedProductList.lean)

The exact uniform one-eighth threshold $223/256$ is therefore attained **only at length 256**. The BLS12-381 example above attains it there. At the other three rates, attainability of the earlier bounds $127/256$, $191/256$, and $479/512$ would likewise require the base length. The unresolved safe steps at those lengths ask about lists with, respectively, 130, 66, and 34 agreements.

At the base length a second locator coefficient also gives one earlier failure whenever the alphabet size is at most $2^{185}$, $2^{163}$, $2^{130}$, or $2^{147}$, respectively. More generally, write $K$ for any embedded field of size $q_0$ with $h\mid(q_0-1)$. If the base-length predecessor passes, then
\[
  \binom{h}{j+2}\le h q_0\lfloor q/2^{128}\rfloor.
\]
The normalized evaluation points are $h$th roots of unity, so they lie in $K$ even if the original coset representative does not. The fixed-product list from the smaller field remains a list over the ambient field. In particular, any sixteenth-rate instance attaining $479/512$ must use more than $309383378205371379825515213835666128450703903$ field elements, and cannot contain a subfield of order at most $826637396689$ whose multiplicative group has order divisible by 512. The corresponding excluded subfield orders extend up to $64191285335851377283423097335403748$ at half rate and $1868751729097317649889$ at quarter rate. Over any subfield containing the required roots, a potential sharp alphabet has relative extension degree at most two at half rate, three at quarter rate, and six at sixteenth rate. [Necessary product inequality and cutoff theorems](../../../ArkLib/Research/ProximityGap/SmoothBaseSubfieldObstruction.lean)

Pairwise packing alone cannot certify those three steps. Apply the existing locator-coloring theorem to 130- and 66-subsets of 256 points with auxiliary field size 257, and to 34-subsets of 512 points with auxiliary field size 521. In each case the binomial count exceeds $2^{128}$ times the square of the auxiliary field size. A largest color thus has more than $2^{128}$ supports, with every pair meeting in fewer than $k$ sites. Whether a single received word can realize such an over-budget family on a given smooth domain is an additional algebraic question. [Support-family theorem](../../../ArkLib/Research/ProximityGap/Frontier/AgreementSupportBarrier.lean)

## A prime-field family of unbounded dyadic length

For every sufficiently large power of two $n$, there exists a prime $p\equiv1\pmod n$ for which the four first bad error counts are $n/2-1$, $3n/4+1$, $7n/8+1$, and $15n/16+1$. The field size in this asymptotic corollary grows exponentially with the length and eventually exceeds the sponsor's preferred 256-bit range.

To see this, let $k=n/2$, $Q=2^{128}$, $A=\binom nk/\binom{k+2}2$, and $L=\binom n{k+1}/n$. Then $L/A=(k+2)/4$. Set $X=2QA$. The estimate $2^n/(n+1)\le\binom n{n/2}\le 2^n$ gives $\log X=\Theta(n)$. The Siegel–Walfisz theorem supplies a prime $p\equiv1\pmod n$ in $(X,2X]$ for every sufficiently large $n$. Indeed $n\le(\log X)^2$ and the main term for the prime count in this interval is of order $X/(\varphi(n)\log X)$, which dominates the uniform error $O(X/(\log X)^4)$. Thus $\lfloor p/Q\rfloor\ge\lfloor A\rfloor$ and $\lfloor p/Q\rfloor\le4A<L$ for large $n$. The binomial criterion with $a=0$ proves the half-rate endpoint. [Walfisz's prime number theorem in arithmetic progressions](https://doi.org/10.1007/BF01218882)

For $k'\in\{n/4,n/8,n/16\}$ one has $\binom n{k'}\le\binom n{n/4}\le 3^{n/4}(4/3)^n$, by evaluating $(1+x)^n$ at $x=1/3$. The base $4/3^{3/4}$ is strictly less than 2, so this quantity is below $A$ for large $n$. Packing at $k'$ agreements is therefore safe. At $k'-1$ agreements the ball about zero contains all $p$ scalar multiples of a locator of degree $k'-1$. The lower and upper counts give the other three endpoints. This asymptotic prime-existence argument is a written application of the classical theorem. The separate finite examples have explicit field certificates.
