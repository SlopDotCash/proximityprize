# Exact thresholds for both challenges at all four rates on sixteen sites

Let $K$ be a finite field with $\lfloor |K|/2^{128}\rfloor=3$ and an element of order 16. Put $p=\operatorname{char}K$ and $f=\operatorname{ord}_{16}(p)$. When $p^f>3\,060\,803\,059\,969$, the first failing closed error counts on every smooth 16-site domain in $K$ are as follows, at every positive interleaving width. The quarter-, eighth- and sixteenth-rate rows hold even without the inequality on $p^f$. The operational supremum in each case is its first failing count divided by 16.

| Rate | Message dimension | First MCA failure | First list failure |
|---|---:|---:|---:|
| $1/2$ | 8 | 3 | 6 |
| $1/4$ | 4 | 3 | 8 |
| $1/8$ | 2 | 3 | 11 |
| $1/16$ | 1 | 3 | 12 |

One example is $K=\mathbb F_{5700000067^4}$ of size $1055600149631724875085666857396420151121$. Here $p\equiv3\pmod {16}$, $f=4$ and the budget is three. The verifier checks primality by trial division, constructs the actual quartic field using a factor of $X^8+1$, and evaluates the explicit witnesses at all sixteen sites. In detail choose $u^2=-2$ in the prime field and adjoin a root of $X^4-uX^2-1$. The defining equation gives $X^8=-1$, and every root of order 16 has degree four over this prime field, proving irreducibility. The table applies whenever $[K:\mathbb F_p(z)]\le3$ for a primitive sixteenth root $z$. [Exact pair ranks and quadratic and cubic examples](mu16-pair-rank-transfer.md) · [Field and all-site verifier](../../../scripts/probes/probe_sixteen_all_rates.py)

## The quarter-rate quartet

Write $z$ for a primitive sixteenth root, and $L_{a,b,c}(X)=(X-z^a)(X-z^b)(X-z^c)$. Use the four words
$$
 0,\qquad L_{0,1,8},\qquad z^2 L_{2,9,10},\qquad
                (z^2+z^4+z^6)L_{1,4,12}.
$$
At each exponent in increasing order choose the center value of the word with the following index, starting the indices at zero:
$$
 0,0,0,1,0,1,1,1,0,0,0,1,0,2,3,2 .
$$
The resulting agreements include all the following sites.

| Word | Eight guaranteed exponents |
|---|---|
| 0 | 0, 1, 2, 4, 8, 9, 10, 12 |
| 1 | 0, 1, 3, 5, 6, 7, 8, 11 |
| 2 | 2, 3, 5, 7, 9, 10, 13, 15 |
| 3 | 1, 3, 4, 11, 12, 13, 14, 15 |

The asserted equalities follow by substituting $z^8=-1$. The three nonzero words have different root sets. The fourth scalar coefficient is nonzero since its value times $L_{1,4,12}(z^3)$ equals $L_{0,1,8}(z^3)\ne0$. Thus the quartet remains distinct in every field admitting the specified root. Four cubics can have at most $16+6\cdot3=34$ total agreements with one center. At any site the agreements beyond the first are bounded by the number of equal pairs, and each of the six pairs agrees at most three times. Four words with nine agreements would require 36. This proves safety at seven errors and failure at eight. The same upper count works for interleaved words by choosing a differing row in each pair. The scalar witness embeds at every positive width. Rescaling the variable and reordering coordinates transports it to each coset. Lean packages both directions into the sponsor’s `GrandListResolution` for every smooth domain of this size over a budget-three field. [Kernel-checked resolution](../../../ArkLib/Research/ProximityGap/Frontier/Mu16CubicList.lean)

The quartet also gives an exact rule on an arbitrary injective grid of size $n$ divisible by four that contains a coset of the sixteenth roots. At dimension four the greatest simultaneous agreement of four words with one center is **$n/4+4$**. Assign $(n-16)/4$ additional sites to each of the four words, independently of their values on the other sites. The pair bound gives $4t\le n+18$, which rounds down to the same integer. This includes grids with no subgroup of order 32. [Previous order-32 construction](cubic-list-padding.md)

## The other rates and the characteristic bound

For dimension two use the four lines $aX+a^{-1}$ with $a\in\{1,z,z^3,z^7\}$. Their six intersections are the six distinct sites $X=(ab)^{-1}$. Each line gains three hits by choosing the repeated value there. The other ten sites supply at least two private hits per line. Four lines with six hits would require 24 total, exceeding $16+6=22$. For dimension one choose four distinct constants and assign four sites to each. Five hits apiece are impossible because their agreement sets are disjoint.

In dimension eight, the support transfer for degree-seven words uses minors over $\mathbb Z[z]$. Every nonzero normalized minor has absolute norm at most $2^{109}$. For an odd prime $p$, reduction at the prescribed root maps $\mathbb Z[z]$ onto the field of $p^f$ elements, since a primitive root first belongs to an extension of degree $f=\operatorname{ord}_{16}(p)$. If a nonzero algebraic integer vanishes there, its principal quotient maps onto this field. Its absolute norm is the order of that finite additive quotient and is divisible by $p^f$. Normalizing the minors removed only powers of two. Thus $p^f>2^{109}$ preserves every nonzero minor and the same all-center support proof applies. The exact lower-order minor norms and the common divisor for the five-row test sharpen the sufficient condition to the bound stated above. [Joint rank certificate](mu16-pair-rank-transfer.md) The resulting list has at most three at five errors and the construction supplies four at six. [Quartet transfer and five-site census](mu16-septic-list-large-characteristic.md)

For all four dimensions $k$, the all-domain MCA theorem applies because $k+3(3-1)\le16$ and $k+3+1\le16$. Every pair is safe at two errors. At three errors the four-site spike gives four distinct bad scalars. [Kernel-checked MCA theorem](../../../ArkLib/Research/ProximityGap/RankExecutable.lean#L302)
