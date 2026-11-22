# The half-rate list threshold on the 128th roots in the 237-bit field

Let $p=126205134105047729256068842055334737587878534445324289139206048206460929$ and let $H$ be the 128th roots of unity in $\mathbf F_p$. Set $B=\lfloor p/2^{128}\rfloor=370883555463132043592346312614163$. The scalar code evaluates polynomials of degree below 64 on $H$.

The computer-assisted bound for every center at 62 errors is $361269899996423739323753777598085$. It is below $B$. At 63 errors the prescribed-product construction exceeds $B$, since $128B<\binom{128}{65}$. Thus the first bad error count is 63. The real-radius condition for safety is $\delta<63/128$. At all four sponsor rates the first over-budget counts are 63, 97, 113 and 121, in decreasing rate order. The lower dimensions use ordinary agreement packing. The explicit modulus and domain generator already have Lean certificates. [Prime and generator](../../../ArkLib/Research/ProximityGap/Frontier/DyadicLogWitness237.lean) · [Lower bound](../../../ArkLib/Research/ProximityGap/Frontier/PrescribedProductList.lean)

## The local calculation

Fix a 61-subset $R\subset H$ and let $U=H\setminus R$, of size 67. Among the list members consider those with exactly two errors on $U$. Each pair of errors determines at most one codeword, since its complement in $U$ contains 65 coordinates. Distinct members have disjoint error pairs on $U$, since the punctured length-67 code has minimum distance four.

For one such word $P$ with error pair $u,v$ set $e_y=P(y)-W(y)$ at $y=u,v$ and $f(x)=(x-u)/(x-v)$. Both error values are nonzero. For any other local member $P'$ with pair $a,b$, the difference $P-P'$ has 63 distinct roots at the other points of $U$. Therefore it is a nonzero scalar multiple of the monic locator of $U\setminus\{u,v,a,b\}$. Evaluate at $u,v$ and divide to obtain

$$
f(a)f(b)=\frac{e_v}{e_u}\prod_{z\in U\setminus\{u,v\}} f(z)=T.
$$

Let $r_{uv}(T)$ count the unordered distinct pairs $a,b$ in **all of** $H\setminus\{u,v\}$ satisfying that equation. The local population for $R$ is at most $1+r_{uv}(T)$. Give this incidence an integer weight of 3 for $r\le1$, 2 for $r=2$, and 0 for $r\ge3$. Give antipodal error pairs weight zero. The total weight at any $R$ is at most 6. Indeed, if the local population is at most two, every weight is at most 3. For population three every weight is at most 2. For population at least four every weight vanishes.

## Counting the samples of a fixed list member

Suppose a word has $e\le62$ errors with support $E$. If $e\le2$, minimum distance 65 makes the entire list a singleton. Otherwise fix two nonantipodal errors $u,v\in E$. There are at least $\binom e2-\lfloor e/2\rfloor$ such unordered pairs. Form $R$ from $E\setminus\{u,v\}$ by adding $l=63-e$ correct sites. Fix all but the last added site, leaving 66 choices for the final site $x$. In the displayed identity the target becomes $\mu/f(x)$ for a nonzero $\mu$ independent of $x$.

Write $c_{uv}(T)$ for the penalty $3$ minus the weight of the incidence. The finite field calculation establishes, for every nonantipodal pair and every nonzero $\mu$,

$$
\sum_{x\in H\setminus\{u,v\}} c_{uv}(\mu/f(x))\le12.
$$

Consequently the 66 choices together contribute at least $3\cdot66-12=186$ weight units. Each $l$-element choice is counted $l$ times by selecting its final element. The total weight of a word is at least

$$
\left(\binom e2-\lfloor e/2\rfloor\right)\binom{128-e}{63-e}\frac{186}{66}.
$$

For the sixty integers $3\le e\le62$ the minimum is $345960=6\cdot57660$, attained at $e=62$. Since all $\binom{128}{61}$ samples carry at most 6 units each, the claimed bound follows.

## Finite certificate and width transfer

The generator $z=g^8$ has order 128 in the certified prime field. A rotation sends a chosen pair to $1,z^d$. Swapping the pair replaces $f$ by $1/f$, which leaves the maximum penalty unchanged after inverting $T$ and $\mu$. Thus $1\le d\le63$ suffices. For each such $d$, compute the 126 distinct ratios, then all unordered pair products and their multiplicities. For every product with a positive penalty $c(T)$, add $c(T)$ to the entry for each $\mu=T f(x)$. An omitted entry has zero penalty. The largest table entry is 9 for each odd separation and 12 for each even separation. This takes exact modular arithmetic in the actual 237-bit field. [Reproducible finite calculation](../../../scripts/probes/probe_dyadic128_two_error_slices.py)

At a positive interleaving width, a list of $B+1$ distinct words has a scalar linear projection retaining their distinctness because $\binom{B+1}{2}\le p$. Projection preserves each agreement with the received word. Conversely the scalar witness at 63 errors embeds diagonally at every positive width. [Lean projection theorem](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListProjection.lean)

Lean proves the ratio identity, weighted sample estimates, complete arbitrary-center count, and both radius directions for all positive widths from the finite histogram. Independent verified replay accepted all 25,374 transitive declarations across those implications. The four-rate Lean wrapper gives the sponsor’s list-decoding prize predicate for this domain from that same histogram. [Four-rate implication](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSlicePrize128.lean)

The Python replay verifies the histogram in the specified field. The Lean kernel checks all six auxiliary rows using only the standard axioms. Cyclotomic transfer carries these bounds to the stated prime interval. [Unconditional sharp thresholds](../../../ArkLib/Research/ProximityGap/Frontier/Smooth128PrimeBand.lean) [Lean threshold](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSliceThreshold.lean) · [Weighted count](../../../ArkLib/Research/ProximityGap/Frontier/TwoErrorSliceCount.lean)
