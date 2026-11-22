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


## A length-1024 obstruction

In the same 237-bit prime field, the larger subgroup generated by $g$ has order 1024. On the row with exponents 0 and 16, take
$$
\mu=17604020721808435999692346832441341307636863595387200509242956284148962.
$$
Thirteen tested sites have at least two admissible pairs each. The site with exponent 18 has at least three, including the pairs $(1,15),(2,14),(3,13)$. Hence this row has total penalty at least $12+3=15$, exceeding the twelve-unit bound used at length 128. The finite proof checks the cleared modular products and the distinctness of all pairs and sites. The obstruction concerns this uniform row bound. [Kernel-verified witness](../../../ArkLib/Research/ProximityGap/Frontier/DyadicPenalty1024.lean)

## The twelve-unit penalty throughout the sponsor prime range

For every prime $p\ge 2^{115}$ and every primitive 128th root in $\mathbb F_p$, all six standard rows have penalty at most twelve. Rotation and an odd change of generator give the same bound for every nonantipodal row. The existing Lean theorem verifies the structural pair transfer used below. The stronger field range for the full weighted comparison has a written proof and an exact integer certificate. The earlier four-rate budget conditions still apply. [Pair transfer](../../../ArkLib/Research/ProximityGap/Frontier/CyclotomicPairDeterminant.lean) · [Weighted certificate](../../../scripts/probes/probe_mu128_charge_heights.py)

Fix the separation $d$ and let $\zeta$ be a complex primitive 128th root. Write $R(x)=(\zeta^x-1)/(\zeta^x-\zeta^d)$. In the auxiliary field of order $167772161$, group the distinct unordered valid pairs by $R(a)R(b)$. Only keys with at least two pairs have a positive charge. For each such key the script verifies in $\mathbb Z[X]/(X^{64}+1)$ that every pair in the fiber has the same product as its first representative. Every auxiliary heavy key thus has a value over the cyclotomic field independent of its chosen representative. Conversely, any pair equality in the source prime field specializes to the auxiliary field, by the pair transfer and $12^{64}<p^2$. These implications identify the heavy keys and their multiplicities in both fields.

For a heavy representative $(a,b)$ and valid tested site $x$, put $t=(a,b,x)$ and take integral coordinates
$$
P_t=\prod_{h\in t}(\zeta^h-1),\qquad Q_t=\prod_{h\in t}(\zeta^h-\zeta^d).
$$
Each factor $1-\zeta^h$ is a unit times $(1-\zeta)^{\gcd(h,128)}$. Indeed $2$ is totally ramified with uniformizer $1-\zeta$, and the absolute norm of the factor is $2^{\gcd(h,128)}$ by the value at 1 of the cyclotomic polynomial of its order. Thus $(1-\zeta)^{v_t}$ divides both coordinates, where $v_t$ is the lesser of the two sums of gcds, at exponents $h$ and $h-d$. Write $H_t$ for the product over all 64 embeddings of the Euclidean norms of these coordinate vectors after division by this common factor. Conjugate embeddings pair, giving the finite formula
$$
H_t=2^{-v_t}\prod_{1\le j<64,\ j\text{ odd}}\left( |P_t(\zeta^j)|^2+|Q_t(\zeta^j)|^2\right).
$$
Here the expressions inside the product mean substitution $\zeta\mapsto\zeta^j$.

Suppose the charge records $s,t$ collide modulo $p$. The cleared comparison $C=P_sQ_t-Q_sP_t$ vanishes at the chosen primitive root. It also vanishes at its inverse, since inversion multiplies every $R(x)$ by the same root of unity and both records have three ratios. These are distinct specializations, so $p^2$ divides the integer norm of $C$. Dividing by $(1-\zeta)^{v_s+v_t}$ leaves the same odd prime divisibility. Complex Cauchy–Schwarz bounds the absolute norm of the quotient by $H_sH_t$. If an integer upper bound for this product is below $2^{230}$, then $C=0$. It consequently vanishes at the auxiliary root as well.

The script bounds each $H_t$ by integer arithmetic. Successive half-angle formulas with outward-rounded integer square roots enclose $2\cos(2\pi j/128)$, hence all squared chord lengths in the display. Sorting these record bounds eliminates every product below $2^{230}$ without enumerating all pairs. For the few remaining comparisons, the script computes the integer norm directly by the quadratic tower recurrence $A(X^2)+XB(X^2)\mapsto A(Y)^2-YB(Y)^2$ and removes the power of two.

| Separation | Heavy-key/site records | Exact norm comparisons | Largest odd-part bit length among these comparisons |
|---:|---:|---:|---:|
| 1 | 23,058 | 1,411 | 195 |
| 2 | 22,302 | 735 | 193 |
| 4 | 22,302 | 111 | 189 |
| 8 | 22,302 | 5 | 188 |
| 16 | 22,302 | 0 | — |
| 32 | 22,806 | 0 | — |

For any source scale with a positive charge, choose one contributing record. Every other contributing record has the same auxiliary scale as the chosen one. The auxiliary charge at that scale is at most twelve, and every charge has the same multiplicity cost in the source and auxiliary fields. This proves the bound. [Verified auxiliary row theorem](../../../ArkLib/Research/ProximityGap/Frontier/AuxiliarySixRows.lean)

## Unrestricted admissible three-ratio comparisons at sponsor size

For $p\ge2^{128}$ the comparison transfer holds for every pair of admissible three-ratio records, including triples whose selected site is also one endpoint of the tested pair. Here a record is any unordered triple of valid sites with at least two distinct entries. Each normalized row has 341,250 such triples. Two equal multisets compare identically. Two distinct triples sharing a site reduce to the two-factor transfer by cancellation. For disjoint triples the program below checks every pair with outward-rounded integer arithmetic. The generic implication from the integer norm sieve to equality in every target field is verified in Lean. The unrestricted finite sweep is checked by the integer program. [Norm sieve theorem](../../../ArkLib/Research/ProximityGap/Frontier/RatioProductNormSieve.lean) · [Complete three-ratio verification](../../../scripts/probes/probe_mu128_triple_transfer.py)

The first filter uses the same projective height bound as for the heavy records. For the remaining pairs, enclose each individual $|P|,|Q|$ between integer multiples of $2^{-16}$ at each of 32 conjugate pairs of embeddings. At embedding $j$, the ratio of the numerator and denominator for a site $x$ is $e^{-\pi i jd/128}$ times a real number of sign
$$
(-1)^{\lfloor jx/128\rfloor-\lfloor j(x-d)/128\rfloor}.
$$
Thus the two crossed terms lie on one real line after a common phase rotation. The intervals give a bound by addition when the two signs differ and by interval subtraction when they agree. The product over the embeddings bounds the norm; remove the lesser of the two exact ramification valuations of the crossed terms. The program uses upward-rounded base-two logarithms in units of $1/256$. Its mantissa bounds use integer bit lengths and integer powers. All fixed-width products stay below $2^{52}$.

| Separation | Pairs surviving the height filter | Disjoint pairs among them | Direct norm checks | Largest odd square-root bit length in direct checks |
|---:|---:|---:|---:|---:|
| 1 | 2,892,583 | 1,828,647 | 47 | 136 |
| 2 | 2,149,586 | 1,333,614 | 32 | 138 |
| 4 | 690,705 | 425,295 | 4 | 134 |
| 8 | 88,200 | 55,252 | 0 | — |
| 16 | 1 | 1 | 0 | — |
| 32 | 5,584 | 5,536 | 48 | 86 |

The remaining 131 norms are computed by the exact quadratic tower recurrence. For each nonzero norm its odd part is explicitly checked to be $s^2$. If $p\mid s$, $p\ge2^{128}$ and $p\ne s$, then $s/p\ge2$ and $s/p\le s/2^{128}$. Removing factors in this range leaves only a possible prime equal to the residual integer itself. Every residual integer at or above the cutoff either has residue different from 1 modulo 128 or has an explicit Fermat compositeness witness. Hence no prime in the stated range admitting a primitive 128th root can divide any nonzero comparison norm twice. Specialization from the source prime to any field of characteristic different from two containing a primitive 128th root follows. The numerical size of the list does not follow from the comparison transfer alone.

### The largest exceptional split prime

The second pass of the three-ratio certificate lowers its search floor to $2^{126}$. Across the six rows it computes 90, 63, 8, 0, 0 and 48 exact norms. Exactly two comparisons survive the prime-factor tests, both at separation one and both at
$$
Q=105018080988161859083316683155074219521.
$$
All admissible comparisons therefore lift over every split prime $p>Q$. The cutoff is sharp. In $\mathbb F_Q$ take $z=34402880081108728517061612743246827085$. This root has order 128. For $d=1$ the triples $(64,64,102)$ and $(37,65,65)$ both give the ratio product $2875244162232378210929075617890627741$. At the auxiliary primitive root their values are $159743306$ and $95344270$. Lean checks primality, root order and the failed transfer, and the independent kernel accepted 7,731 declarations for these three results. The weighted twelve-unit penalty still holds at $Q$ by the heavy-record computation, which works at every $p\ge 2^{115}$. [Exact witness](../../../ArkLib/Research/ProximityGap/Frontier/Mu128ExceptionalTriple.lean) · [Sharp upper sweep](../../../scripts/probes/probe_mu128_triple_transfer.py)
