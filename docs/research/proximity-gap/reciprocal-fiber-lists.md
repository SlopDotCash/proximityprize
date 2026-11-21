# Longer agreements for large lists on the two named prime fields

At length $n=2^{30}$ the following error counts already produce more than $B=\lfloor p/2^{128}\rfloor$ distinct scalar Reed–Solomon codewords in one closed ball. They apply to every positive interleaving width by repeating a scalar row. The gains count additional agreements relative to the prescribed-product construction at the same quotient order. The error counts are upper bounds on first failure. A matching bound on lists about every center is open.

A subsequent two-anchor construction improves the half-rate entries below to **500520279** and **502025926** first-failure ceilings. [Signed two-anchor bounds](signed-two-anchor-lists.md) At rate $1/16$, an exact count of overlapping pools at fifteen anchors gives ceilings **989855735** and **989855741**. [Fifteen-anchor construction](sixteenth-locator-union.md)

| Named field | Budget | Rate | Quotient order $M$ | Gain | First failure at or before |
|---|---:|---:|---:|---:|---:|
| First | $2^{30}$ | $1/2$ | 64 | 2,097,152 | 501,219,329 |
| Second | $2^{31}$ | $1/2$ | 64 | 1,198,372 | 502,118,109 |
| First | $2^{30}$ | $1/4$ | 64 | 6,978 | 771,744,959 |
| Second | $2^{31}$ | $1/4$ | 64 | 2,789 | 771,749,148 |
| First | $2^{30}$ | $1/8$ | 128 | 262,144 | 922,484,737 |
| Second | $2^{31}$ | $1/8$ | 128 | 135,300 | 922,611,581 |
| First | $2^{30}$ | $1/16$ | 128 | 4 | 989,855,741 |
| Second | $2^{31}$ | $1/16$ | 128 | 1 | 989,855,744 |

The first prime is $365375409332725729550921208179070755120141565953$. The second is $730750818665451459101842416358141509841924915201$. The construction works on any multiplicative coset of the same order in a field with the indicated budget. Precomposing a polynomial with multiplication by the coset representative or its inverse preserves its degree and transports agreements bijectively. [First field certificate](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30.lean) · [Second field certificate](../../../ArkLib/Research/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean)

## Assigning extra agreements

Write $n=Mh$ and $k=bh$. Fix a generator $u$ of the quotient group $\mu_M$. For each $(b+1)$-subset $T$ of $\mu_M\setminus\{1,-1\}$, put $L_T(Y)=\prod_{z\in T}(Y-z)$. Suppose a collection of more than $B$ such subsets shares the same root product. This fixes $c=L_T(0)$. The polynomials
\[
Q_T(Y)=\frac{Y^{b+1}+c-L_T(Y)}{Y}
\]
have degree at most $b-1$ because the leading terms cancel and the numerator vanishes at zero. Let $H$ be the monic polynomial vanishing at $h-1$ sites of the fiber $x^h=-1$. The lifted word for $T$ is $f_T(X)=H(X)Q_T(X^h)$, of degree at most $bh-1$. On the order-$n$ group set
\[
w(x)=H(x)\frac{(x^h)^{b+1}+c}{x^h}.
\]
Each candidate agrees on all $h(b+1)$ sites over $T$ and at the $h-1$ chosen roots of $H$. Different subsets give different polynomials and hence different evaluation words since their degrees are below $n$. These are the prescribed-product and common-root steps in Al Kindi's Theorem 1.1. [Al Kindi, ePrint 2026/2245](https://eprint.iacr.org/2026/2245)

Suppose the values $L_T(1)$ take at most $2K$ values in this collection. On the previously unused fiber $x^h=1$, allot $\lfloor h/(2K)\rfloor$ distinct sites to each possible value $v$. At a site allotted to $v$ replace $w(x)$ with $H(x)(1+c-v)$. Every candidate gains its allotted sites while all its preceding agreements survive. This yields at least
\[
(b+2)h-1+\lfloor h/(2K)\rfloor
\]
agreements per candidate about a single received word.

## Counting root sets with few locator values

For $z\ne0$ write $N(z)=(1-z)(1-z^{-1})$. With $m=b+1$ the identity
\[
 L_T(1)^2=(-1)^m\left(\prod_{z\in T}z\right)\prod_{z\in T}N(z)
\]
shows that fixing the root product and the product of the $N(z)$ gives at most two values at one. The identities $N(z)=N(z^{-1})$ and $N(z^2)=N(z)N(-z)$ make the norm product countable with a small binary tree.

For $M$ a power of two at least four, index all inverse pairs in $\mu_M\setminus\{1,-1\}$ by $j=1,\ldots,M/2-1$, representing the roots $u^{\pm j}$. The tree has root $M/4$. An even node $j$ has children $j/2$ and $(M-j)/2$, and odd nodes are leaves. Let $a_j\in\{0,1,2\}$ be the number of selected members of the pair. For each leaf $i$ let $v_i$ be the sum of the $a_j$ along its path from the root. Applying the doubling identity at internal nodes gives
\[
 \prod_{z\in T}N(z)=\prod_{i\text{ leaf}}N(u^i)^{v_i}.
\]
The integer vector $v$ also fixes the parity of the exponent of the root product. Only odd-indexed pairs contribute to that parity, and each internal node has an even number of descendant leaves. Both parities are therefore $\sum_i v_i\bmod 2$.

For fixed leaf sums $v$, let $A_v(X)$ count subsets by cardinality. At a leaf with entry $a\in\{0,1,2\}$ it is $\binom2a X^a$. An inadmissible leaf or any negative entry gives zero. At an internal node with left and right vectors $l,r$,
\[
 A_{(l,r)}(X)=\sum_{a=0}^2\binom2a X^a A_{l-a}(X)A_{r-a}(X),
\]
where the subtraction is entrywise. The formula counts the two orientations of a singleton and the unique choices for zero or two roots. Distinct vectors classify disjoint subsets, even if their products in the field happen to coincide.

Take $K$ different vectors of one parity with a total of $S$ subsets of size $b+1$. At most $M/2$ root products are possible. If $S>(M/2)B$, a single product class exceeds budget. Within that class each vector permits at most two values of $L_T(1)$, as required in the construction above.

| Field | Rate | $K$ | Parity | $S$ | $(M/2)B$ |
|---|---:|---:|---:|---:|---:|
| First | $1/2$ | 4 | even | 40,848,673,100 | 34,359,738,368 |
| Second | $1/2$ | 7 | even | 69,062,504,660 | 68,719,476,736 |
| First | $1/4$ | 1,202 | odd | 34,373,808,256 | 34,359,738,368 |
| Second | $1/4$ | 3,007 | odd | 68,733,805,280 | 68,719,476,736 |
| First | $1/8$ | 16 | odd | 71,406,303,776 | 68,719,476,736 |
| Second | $1/8$ | 31 | odd | 138,349,713,566 | 137,438,953,472 |

The verifier takes the largest coefficients of each parity from explicitly bounded families of integer vectors. At half rate it varies at most two entries of the constant vectors 4, 5 or 6 by one. At quarter rate it varies at most three entries of the constant vector 3 by one. At eighth rate it varies at most one entry of the constant vectors 1, 2 or 3 by one. The script independently enumerates all quotient subsets on three small boards, compares their counts with the recurrence and evaluates the constructed polynomials at every site. [Reproducible verifier](../../../scripts/probes/probe_reciprocal_fiber_lists.py)

Lean verifies the squared locator and norm doubling identities, the lifted polynomial’s degree and exact agreements with the original center, and the allocation of a common received word on a spare fiber. The full numerical bounds above use the written construction and the executable recurrence. [Lean lemmas](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalFiberLists.lean)

## Seven spare fibers at rate one sixteenth

Here $M=128$, $b=8$ and $h=2^{23}$. Take all nine quotient roots of each $T$ outside the order-eight subgroup $S$ of $\mu_{128}$. Reserve the $h-1$ roots of $H$ over 1. The seven other elements of $S$ can now supply extra agreements to disjoint collections of candidates. The same specified locator constant and original center work across all seven collections.

For $T$ define $W(T)=\sum_{u^j\in T}\gcd(j,16)$. Because $16\nmid j$, each summand equals $2^{v_2(j)}$, the number of leaves below the node for $u^{\pm j}$. Consequently $W(T)$ is the sum of the entries of its leaf vector. Rotating $T$ by an element of $S$ changes exponents by a multiple of 16 and preserves $W$. Fix a parity $p_0$ and assign every $T$ with $W(T)\equiv p_0+2i\pmod{14}$ to the $i$th spare node $y_i$ for $0\le i<7$. The choice of enumeration of the seven nodes is arbitrary. The sets assigned to different nodes are disjoint.

At $y_i$ compute the leaf vector of $T/y_i$. Its sum has the same residue as $W(T)$. For a desired gain $g$ retain the $\lfloor h/(2g)\rfloor$ most numerous vectors in this residue class, or all of them if fewer exist. Their populations can be computed at 1 because rotation by $y_i$ permutes $\mu_{128}\setminus S$. Every retained subset has root product with exponent of parity $p_0$. If the total population across the seven nodes is $A$, one root product occurs for at least $\lceil A/64\rceil$ subsets. In that common product class, the product of the roots of $T/y_i$ is fixed on each node. The squared-locator identity bounds the number of values of $L_T(y_i)=y_i^9 L_{T/y_i}(1)$ by twice the number of retained vectors for $y_i$.

Assign $g$ sites over $y_i$ to each such locator value $v$. At those sites put $w(x)=H(x)(y_i^9+c-v)/y_i$. All earlier agreements over the nine ordinary quotient roots and the $h-1$ reserved roots survive. Each candidate gains at least $g$ additional sites at its assigned node.

| Budget | $p_0$ | $g$ | Retained subsets $A$ | Guaranteed distinct codewords |
|---:|---:|---:|---:|---:|
| $2^{30}$ | 1 | 4 | 73,013,231,360 | 1,140,831,740 |
| $2^{31}$ | 0 | 1 | 198,924,785,832 | 3,108,199,779 |

Removing the forbidden nodes leaves four binary trees of eight leaves each. The verifier enumerates possible leaf vectors in one tree through degree nine up to swaps of children. Each unequal pair of child shapes gives two orderings. Multiplying the resulting orbit sizes recovers every labelled vector. For each residue and coefficient polynomial it stores the number of such vectors. It multiplies the four trees' polynomials, adding residues modulo 14, to obtain the number of vectors with each possible population of nine-subsets. The total mass across all vectors equals $\binom{120}9$. Ranking by the degree-nine coefficient in each residue gives the table. Independent small tests compare complete histograms to exhaustive subset enumeration and build one received word with candidates assigned to multiple fibers. Lean proves that subgroup rotations preserve the sum of the gcd weights and that all local fiber assignments can be combined into one received word. The production arithmetic uses the executable census. [Verifier](../../../scripts/probes/probe_multifiber_sixteenth_lists.py) · [Lean allocation](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalFiberLists.lean)
