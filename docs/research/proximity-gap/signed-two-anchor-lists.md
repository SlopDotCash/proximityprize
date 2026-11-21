# Over-budget half-rate lists from two signed locator values

Let $n=2^{30}$ and $k=n/2$. On the order-$n$ multiplicative subgroup of each designated prime, one received word has the following list of distinct degree-$<k$ polynomials. The construction transports to every multiplicative coset by a change of variable and to every positive interleaving width by repeating the same row.

| Field | 128-bit budget | Guaranteed list size | First failure at or before | Reduction from the previous ceiling |
|---|---:|---:|---:|---:|
| First | 1,073,741,824 | 1,082,787,054 | 500,520,279 errors | 699,050 |
| Second | 2,147,483,648 | 2,183,824,781 | 502,025,926 errors | 92,183 |

The previous one-anchor proof bounded each locator value up to sign and placed the common vanishing roots on a single fiber. Here the exponent sum resolves that sign. Dividing the common roots between two fibers leaves enough space for either fiber to contribute agreements to the same list. The table records populations from the explicit signed-residue certificate below. Lean independently proves both error ceilings by averaging over the product class and the signs used at the two anchors. The universal safe half-rate count through 314491699 errors continues to hold on both fields. [One-anchor construction](reciprocal-fiber-lists.md) · [Safe list bound](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListJohnsonRank.lean) · [Signed locator lemmas](../../../ArkLib/Research/ProximityGap/Frontier/SignedReciprocalLists.lean) · [Verifier](../../../scripts/probes/probe_signed_two_anchor_lists.py)

The complete implication from a counted quotient family to distinct codewords in one production ball is now kernel-checked, including both anchor-value sets, the common roots and positive widths for the cyclic fixed-product bound. Without the signed census Lean proves first-failure ceilings **503316481, 771751937, 922746881 and 989855745** at the four rates on each of the two designated subgroups. These unconditional formal bounds apply to every budget through 128644068888 on every full cyclic subgroup of the same length in a finite field. The signed half-rate proof guarantees at least **1,082,868,236** and **2,183,676,021** distinct words at the two smaller radii in the table. [Full two-anchor list construction](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean) · [Four-rate formal bounds](../../../ArkLib/Research/ProximityGap/Frontier/NamedProductionLists.lean) · [Signed half-rate bounds](../../../ArkLib/Research/ProximityGap/Frontier/SignedNamedLists.lean)

## The two fibers share one center

Put $M=64$, $h=n/M=16777216$, $b=32$ and $m=b+1$. Write $Y=X^h$ and take $T$ to be an $m$-subset of the quotient roots $\mu_M\setminus\{1,-1\}$. Let $L_T(Y)=\prod_{a\in T}(Y-a)$. Fix a common root product, hence a common $c=L_T(0)$. Then
$$
 Q_T(Y)=\frac{Y^m+c-L_T(Y)}Y
$$
is a polynomial of degree at most $b-1$. At either anchor $y=1,-1$, one value of $L_T(y)$ determines $Q_T(y)$.

Suppose the required candidate family consists of the union of those with one of $K_+$ specified values or signatures at $+1$ and those with one of $K_-$ at $-1$, each signature determining one value. Set $g=\lfloor(h+1)/(K_++K_-)\rfloor$ and assume $K_+g,K_-g\le h$. Allocate $g$ disjoint positions at the corresponding anchor fiber to each signature. From the two fibers together at least $2h-(K_++K_-)g\ge h-1$ positions remain. Choose $h-1$ of these and let $H$ be their monic vanishing polynomial.

The word for $T$ is $f_T(X)=H(X)Q_T(X^h)$ of degree at most $bh-1$. Define the received value off the allocation by $H(x)(y^m+c)/y$, where $y=x^h$. On a group of sites allocated to a locator value $v$ use $H(x)(y^m+c-v)/y$. All candidates agree on the $mh$ positions over their quotient roots and the $h-1$ roots of $H$. Each selected candidate gains at least $g$ additional agreements in one of the two fibers. Different sets give different polynomials because $H$ and $c$ are fixed. Their degree is below $n$, so their evaluation words are distinct.

## Signed values and joint populations

Choose a primitive $2M$-th root $z$ and put $i=z^{M/2}$, so $i^2=-1$. Represent a quotient root by $z^{2j}$ with $1\le j<M$, $j\ne M/2$. Its weight $W_j=i(z^{-j}-z^j)$ satisfies
$$
 1-z^{2j}=(-i)z^jW_j,\qquad W_{M-j}=W_j,\qquad W_{2j}=W_jW_{M/2-j}.
$$
The last identity follows by multiplying out, with $z^{M/2-j}=i/z^j$. Thus $L_T(1)$ equals $(-i)^m z^{\sum j}$ times a product of weights at odd leaves. Group inverse pairs under $j\mapsto M-j$. The tree has root $M/4$ and children $j/2,(M-j)/2$ at each even node. Each pair contributes its occupancy $0,1,2$ to the exponent of every odd leaf below it. Write $v$ for the vector of these exponents in left-to-right tree order and $e=\sum j\pmod{2M}$. Then $(v,e)$ determines a single signed locator value. Its root product is $z^{2e}$. The minus-anchor signature is computed on the exponents shifted by $M/2$ modulo $M$, since $L_T(-1)=(-1)^m L_{-T}(1)$.

For the single-signature census, at node $j$ an occupancy $a$ contributes orientations with exponent sums $0$ for $a=0$, $j,M-j$ for $a=1$, and $M$ for $a=2$. Subtract $a$ from every entry beneath the node and convolve the child counts by cardinality and exponent modulo $2M$. For the joint census prescribe both leaf vectors. Negation fixes the root pair and swaps the two child pair indices at every node. If the original occupancies of the children are $c,d$, their rotated occupancies are $d,c$. Subtract the prescribed original and rotated occupancies from their respective vectors, recurse on $(c,d)$ at the left and $(d,c)$ at the right, and count the orientations of the original set once. The terminal leaf accepts precisely its two prescribed occupancies. This counts each subset giving the two signatures, retaining the original exponent sum.

For reproducibility write $A=(5^{16})$, $B=(6^8,5^8)$, $C=(5^8,6^8)$, $D=(5^{12},6^4)$, where exponents indicate repetitions. The original and rotated exponent sums listed below are residues modulo 128. Each row fixes one original product because negation adds $33\cdot32$ to the exponent modulo 64.

| Field | Plus-anchor modes | Minus-anchor modes |
|---|---|---|
| First | $A:56,120$ and $C:56$ | $A:24,88$ and $B:24$ |
| Second | each of $A,B,C:60,124$ | each of $A,B,C:28,92$ and $D:28$ |

The rows below give exact single-anchor populations. For the overlap we discard the rotated exponent condition while retaining the rotated leaf vector and original signed mode. Summing over the distinct rotated vectors and the original modes yields an upper bound on the full intersection.

| Field | Plus population | Minus population | Overlap at most | Distinct words at least | Extra agreements $g$ |
|---|---:|---:|---:|---:|---:|
| First | 545,514,807 | 545,514,807 | 8,242,560 | 1,082,787,054 | 2,796,202 |
| Second | 1,035,846,314 | 1,193,490,135 | 45,511,668 | 2,183,824,781 | 1,290,555 |

A separate Lean certificate counts the 33-root selections for each leaf signature before fixing the exponent. On the common 31-node layout the populations of $A,B,C,D$ are **12,219,257,340**, **10,463,808,348**, **10,463,808,348**, and **10,080,571,912**. Negating roots exchanges the sibling occupancies and preserves the number selected. Among the twelve intersections with original signature $A,B,C$ and rotated signature $A,B,C,D$, the nonzero counts are $237308948$ for $(A,A)$, $556624096$ for each of $(B,B),(C,C)$, and $52922120$ for each of $(B,C),(C,B)$. Each entry follows by checking 43 finite tables against the dyadic recurrence and extracting the size-33 digit in radix $2^{64}$. The proof uses these aggregate counts directly. [Common mask space and rotation](../../../ArkLib/Research/ProximityGap/Frontier/QuotientMaskSelections.lean) · [Kernel-checked tables](../../../ArkLib/Research/ProximityGap/Frontier/QuotientSignatureTables.lean)

For a mask with any of the four selected signatures, the ordinary exponent sum is even. This follows by evaluating its norm tree with every leaf equal to $-1$: the product for each selected signature is $1$. The root product consequently has 32 possible exponents modulo 64. In a fixed product class the squared locator value at each anchor depends only on its signature. The two named fields satisfy all 62 factor identities used by the norm trees, so a representative and its negative cover every actual value in that class. [Parity and squared values](../../../ArkLib/Research/ProximityGap/Frontier/QuotientMaskLocator.lean) · [Named-field identities](../../../ArkLib/Research/ProximityGap/Frontier/QuotientMaskPrimeNorms.lean)

Allocate the two signs of a signature, a single sign, or neither according to the table of plus and minus modes above. Vary the product class and the two single-sign choices independently, giving $32·2·2=128$ configurations. A mask with $a$ allowed plus signs and $b$ allowed minus signs contributes $2a+2b-ab$ to the sum of union sizes. The exact single and intersection counts give total multiplicities **138,607,134,200** and **279,510,530,592**. Some configuration therefore retains at least **1,082,868,236** and **2,183,676,021** distinct root sets, respectively. Their common product fixes the locator constant. The first allocation uses at most three values per anchor and the second uses at most six and seven. Applying the shared-center construction gives the stated error ceilings on the actual length-$2^{30}$ domains. [Counting proof](../../../ArkLib/Research/ProximityGap/Frontier/QuotientMaskBudget.lean) · [Actual locator values](../../../ArkLib/Research/ProximityGap/Frontier/QuotientAnchorAllocation.lean) · [Named codeword bounds](../../../ArkLib/Research/ProximityGap/Frontier/SignedNamedLists.lean)

Subtracting $(m+1)h-1+g$ from $n$ gives the two error counts. The verifier also exhausts all five-subsets of the ordinary roots at quotient order 16, compares every joint signature including zero counts to direct enumeration, and evaluates a two-anchor list on every point of the order-128 subgroup over $\mathbb F_{257}$. [Exact integer recurrence and small reconstruction](../../../scripts/probes/probe_signed_two_anchor_lists.py)

## Fourteen budgets on arbitrary smooth domains

The same two-anchor argument works over every finite field admitting a smooth domain of length $2^{30}$. For a quotient generator $z$ one has $z^{32}=-1$. The identities for $N(j)=(1-z^j)(1-z^{64-j})$ are $N(2j)=N(j)N(32-j)$ and $(1+z^j)(1+z^{64-j})=N(32-j)$. Induction down the tree proves all 62 signed factor identities directly in the field. Every smooth domain at this length is a permuted multiplicative coset of the full subgroup. Scaling the polynomial variable preserves the degree bound, and permuting coordinates carries the center and its entire list to the supplied domain. [Uniform norm proof and allocations](../../../ArkLib/Research/ProximityGap/Frontier/UniversalSignedListNorms.lean) · [Smooth-domain theorem](../../../ArkLib/Research/ProximityGap/Frontier/SmoothSignedListProfile.lean)

Each row gives a closed half-rate ball with at least the stated population, at every positive interleaving width. It bounds the first-failure error count whenever the integer budget is strictly below that population.

| Signed anchor values | Distinct words at least | Errors at most |
|---:|---:|---:|
| 1 | 190,925,896 | 486,539,265 |
| 2 | 381,851,792 | 494,927,873 |
| 3 | 569,069,736 | 497,724,076 |
| 4 | 756,287,680 | 499,122,177 |
| 5 | 919,784,685 | 499,961,038 |
| 6 | 1,083,281,690 | 500,520,279 |
| 7 | 1,246,778,696 | 500,919,736 |
| 8 | 1,410,275,701 | 501,219,329 |
| 9 | 1,567,784,637 | 501,452,346 |
| 10 | 1,725,293,574 | 501,638,760 |
| 11 | 1,879,266,419 | 501,791,280 |
| 12 | 2,033,239,265 | 501,918,380 |
| 13 | 2,187,212,111 | 502,025,926 |
| 14 | 2,341,184,957 | 502,118,109 |

The sixth and thirteenth allocations raise the kernel-checked population guarantees at the two designated budgets to **1,083,281,690** and **2,187,212,111**. The proofs apply to every smooth domain at the same field order and length, including arbitrary coset representatives and coordinate orderings. Independent replay of the earlier named-domain bounds in [PR #634](https://github.com/SlopDotCash/proximityprize/pull/634) accepted all 25,902 transitive declarations.

## Why agreement incidence alone stops at the first quarter-rate successor

At first-prime rate $1/4$ the current universal safe count is $n/2+1$. At the next count, an abstract family respecting all pairwise agreement constraints can already have **$2(n-5)>n$** members. Take $q=536870909$, a prime congruent to one modulo four. Paley's type-II construction gives a Hadamard matrix of order $v=2(q+1)=n-4$. Normalize its first row to be all positive. Each other row and its negative has balanced positive support of size $v/2$. For different nonopposite rows, orthogonality gives exactly $v/4$ joint positives. Opposite rows have disjoint supports. Extending each support with four unused coordinates gives the required $n$-site family, each block of size $n/2-2$ and each overlap at most $n/4-1=k-1$. The verifier checks primality by trial division. Any stronger safe result here must use restrictions on Reed–Solomon agreement families beyond block size and pairwise intersections. Whether such a family is realizable by actual words remains open. [Paley, *On Orthogonal Matrices* (1933)](https://doi.org/10.1002/sapm1933121311)
