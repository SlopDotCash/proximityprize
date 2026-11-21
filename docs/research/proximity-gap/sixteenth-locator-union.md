# Overlapping locator lists at rate one sixteenth

At length $n=2^{30}$ and dimension $2^{26}$, the first and second designated prime fields have the following upper bounds on the first error count at which a single received word has more than $B=\lfloor p/2^{128}\rfloor$ codewords in its closed Hamming ball. The scalar lists lift to every positive interleaving width by repeating the same row in the center and each candidate. The construction applies on any multiplicative coset of order $n$ over a field with the indicated budget.

| Field | Budget $B$ | Signatures per anchor | Anchor incidences | Distinct candidates | Gain $g$ | First failure at or before |
|---|---:|---:|---:|---:|---:|---:|
| First | 1,073,741,824 | 517,954 | 1,551,671,296 | 1,132,216,224 | 8 | **989,855,737** |
| Second | 2,147,483,648 | 1,398,090 | 3,367,652,416 | 2,459,641,984 | 3 | **989,855,742** |

The earlier seven-anchor ceilings were 989,855,741 and 989,855,744. The exact first failing counts remain open on both domains. [Previous construction and prime certificates](reciprocal-fiber-lists.md)

## One center at all fifteen anchors

Set $M=128$, $h=n/M=2^{23}$, and let $u$ generate the quotient group $\mu_M$ obtained as the image of $x\mapsto x^h$ on $\mu_n$. The exponents of the subgroup $S=\mu_{16}$ are the multiples of eight. Take nine-element subsets $T$ of $\mu_M\setminus S$ with $\prod_{z\in T}z=1$. Their locators $L_T(Y)=\prod_{z\in T}(Y-z)$ all have constant coefficient $c=-1$. Put

\[
Q_T(Y)=\frac{Y^9+c-L_T(Y)}{Y},\qquad f_T(X)=H(X)Q_T(X^h),
\]

where $H$ is monic and its roots are exactly $h-1$ sites of $x^h=1$. Leading and constant terms cancel in the numerator, so $\deg f_T\le 8h-1<k$. The baseline center $w(x)=H(x)((x^h)^9+c)/x^h$ agrees with $f_T$ on the $9h$ points with $x^h\in T$ and on the $h-1$ roots of $H$. Distinct $T$ give distinct locators and hence distinct $f_T$ by injectivity of substitution and cancellation of $H$. Evaluation preserves distinctness since $\deg f_T<n$. Scaling $X$ transports both the center and candidates to any coset.

For each $y\in S\setminus\{1\}$ classify $T/y$ by its vector $v$ of 32 leaf sums in the reciprocal-pair tree. For $N(z)=(1-z)(1-z^{-1})$, the identities $N(z)=N(z^{-1})$ and $N(z^2)=N(z)N(-z)$ express the product of the $N(z)$ over $T/y$ using only $v$. Since $\prod_{z\in T/y} z=y^{-9}$, the identity

\[
  L_{T/y}(1)^2=(-1)^9y^{-9}\prod_{z\in T/y}N(z)
\]

gives at most two possibilities for $L_T(y)=y^9L_{T/y}(1)$ at fixed $y,v$. Select $b$ vectors at each anchor. Inside its $h$ sites allocate $g=\lfloor h/(2b)\rfloor$ sites for each of the at most $2b$ distinct locator values $l$. Use $H(x)(y^9+c-l)/y$ as the received value on the sites allotted to $l$. This specifies one center. The allocated coordinates at all fifteen anchors are disjoint from all $9h+(h-1)$ baseline agreements. Every $T$ with a selected vector at one or more anchors has at least $10h-1+g$ agreements, giving the two displayed ceilings. The allocations use at most 8,287,264 and 8,388,540 of the 8,388,608 sites per anchor.

## Counting the union exactly

A vector's score is its number of nine-subsets before imposing the product. The 112 ordinary roots form eight disjoint reciprocal-pair trees of four leaves each. The node occupancy $a\in\{0,1,2\}$ adds $a$ to every descendant leaf and contributes the factor $\binom{2}{a}X^a$ to its size enumerator. The coefficient of $X^9$ after multiplying the eight subtrees' enumerators is the score. The verifier generates all labelled vectors with even leaf sum and score greater than 7,680. The parity constraint follows from the even exponent of $y^{-9}$ and the fact that an internal node has an even number of leaves. It produces 1,923,274 distinct vectors. [Reciprocal-pair recurrence](reciprocal-fiber-lists.md#counting-root-sets-with-few-locator-values)

The first pool consists of all scores greater than 9,504. The second takes all scores greater than 8,192, then whole odd-multiplier orbits at score 8,192 up to capacity $\lfloor h/6\rfloor=1,398,101$. The verifier orders tied orbits by the least unsigned integer encoding of a member and skips orbits larger than the remaining capacity. The encoding places the tree's first leaf in the least significant four bits, visiting the child $j/2$ before $(M-j)/2$. Multiplication of exponents by any odd $u'$ permutes the leaves, fixes the required product 1, and permutes the fifteen nonidentity anchors. Both pools are invariant under this action.

For each anchor exponent $a$ and selected vector, enumerate all nine-subsets of relative exponents with that vector and sum $-9a\bmod128$. Adding $a$ to each relative exponent gives exactly the desired original root sets of product 1. The verifier forms local subsets on the fourteen ordinary sites in each tree, joins their masks by leaf sum, and imposes the size and residue conditions. It enumerates one representative for each orbit of anchor-vector pairs and multiplies by the orbit size. The anchor representatives $a=8,16,32,64$ have orbit sizes $8,4,2,1$. Inside a fixed anchor it uses precisely the odd multipliers fixing that anchor.

For every such incidence the verifier recomputes the vectors at all fifteen anchors. If $T$ occurs at $j$ anchors in the pool, add $D/j$, where $D=\operatorname{lcm}(1,\ldots,15)=360360$. Each admitted $T$ contributes exactly $D$ over all its incidences. This weight is invariant under odd multipliers. Dividing the orbit-weighted sum by $D$ gives the table’s number of distinct candidates. The full count fits unsigned 64-bit arithmetic since $D\binom{112}{9}=1,980,020,864,777,155,200<2^{64}$. Lists obtained by changing the fixed root product would have a different common constant $c$ in the baseline center. Their cardinalities cannot simply be added to this construction.

## Reproduction

Run the following from the repository root with Python 3 and a C++17 compiler supporting unsigned 128-bit integers. The program builds in a temporary directory. Select one to three workers.

```sh
python3 scripts/probes/check_sixteenth_locator_union.py --workers 3
```

The controls enumerate all 220 root sets at $(M,|S|,m)=(16,4,3)$ and all 42,504 at $(32,8,5)$. They compare every retained labelled vector and its score with the size recurrence. They independently choose the tied orbits by multiplying actual root exponents, count union sizes by direct membership, and compare these results with the C++ census. On the smaller board all four selected polynomials are also evaluated over the entire length-1,024 domain in $\mathbb F_{65537}$. The smallest actual agreement count is 285. The production output is

```text
orbits=421270 denominator=360360
bins=517954 incidences=1551671296 unique=1132216224
bins=1398090 incidences=3367652416 unique=2459641984
budget=1073741824 list=1132216224 gain=8 first_bad<=989855737
budget=2147483648 list=2459641984 gain=3 first_bad<=989855742
```

Lean proves the locator and fiber-allocation identities. The production union sizes use the executable integer census. [Allocation lemmas](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalFiberLists.lean) · [Pool generator and independent controls](../../../scripts/probes/check_sixteenth_locator_union.py) · [Exact union census](../../../scripts/probes/probe_sixteenth_locator_union.cpp)
