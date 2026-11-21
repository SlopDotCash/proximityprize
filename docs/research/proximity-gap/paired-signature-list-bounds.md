# Counting both locator signatures at the named production primes

At length $n=2^{30}$, the following closed Hamming balls contain more Reed–Solomon words than the $2^{-128}$ budget. Each row bounds the first failing error count from above. The construction uses one center per row and works at every positive interleaving width. The earlier ceilings use the same three or seven serving fibers and assign each signature class to a single anchor. Here two opposite anchors can serve the same class. [Previous serving-fiber construction](oriented-fiber-list-bounds.md) · [Formal conversion of quotient sets into codewords](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean)

| Prime | Rate | Budget | Distinct words guaranteed | Previous ceiling | New ceiling |
|---|---:|---:|---:|---:|---:|
| First | $1/4$ | 1,073,741,824 | 1,074,846,561 | 771,733,023 | **771,731,452** |
| Second | $1/4$ | 2,147,483,648 | 2,147,931,768 | 771,745,290 | **771,743,163** |
| First | $1/8$ | 1,073,741,824 | 1,096,617,376 | 921,698,305 | **921,348,780** |
| Second | $1/8$ | 2,147,483,648 | 2,165,162,624 | 922,253,434 | **922,047,831** |

## The common center

Write $n=Mh$, with $M=64$ or $128$, and let $z$ generate the quotient of order $M$. Reserve the subgroup of order $R$, with $R=4$ at quarter rate and $R=8$ at eighth rate. Its exponents are $aM/R$ for $0\le a<R$. Use $17$-subsets $T$ of the remaining roots, with exponent sum $r$ modulo $M$. The constant term $c$ of $L_T(Y)=\prod_{u\in T}(Y-u)$ is fixed. The polynomial $Q_T(Y)=(Y^{17}+c-L_T(Y))/Y$ has degree at most 15. Multiply $Q_T(X^h)$ by the monic polynomial $H$ vanishing on $h-1$ sites over the last reserved root, at $a=R-1$. The product has degree below $16h$, and the received word $H(X)((X^h)^{17}+c)/X^h$ agrees with it on $17h$ ordinary sites and the $h-1$ common roots.

At each of the first $R-1$ reserved roots retain $K$ signature classes. A class for anchor $a$ is computed after rotating the exponents by $-aM/R$. It fixes $L_T$ at that anchor by the signed locator identity and the same rotation. Assign $\lfloor h/K\rfloor$ different sites to each class to match its codewords. Distinct ordinary agreement fibers distinguish the words even after those edits. Every subset in the union of the retained collections produces a word with at least $18h-1+\lfloor h/K\rfloor$ agreements. Repeating its row gives the same construction at positive width. [Signed identity and its specialization to the prime fields](oriented-fiber-list-bounds.md#the-locator-value-at-the-spare-fiber)

## Bounding the overlap

The inverse pair indexed by $j$ consists of $z^j,z^{-j}$ for $1\le j<M/2$. At an even node its children are $j/2,(M-j)/2$. Multiplication by $-1$ exchanges the occupancies of sibling nodes and fixes the occupancy of the root. Each leaf entry of a signature counts the occupied roots along the path to that leaf. Each signed class also specifies the sum of the ordinary exponents modulo $2M$.

For a subtree with $s$ leaves, let $a,b$ be its inherited path sums for $T,-T$. The sum of its prescribed positive leaf entries minus the sum of its prescribed negative entries equals $s(a-b)$. Indeed, sibling occupancies exchange, and the children have equal numbers of leaves. Their new contributions cancel when summed. On a single leaf the claim follows from its two path sums. At the root the total sums agree. On every smaller subtree the two totals agree modulo the number of leaves. Comparing all these residues discards impossible pairs of signatures. Lean proves this directly for the established tree acceptance predicate, including that incompatible subtrees contribute zero to its weighted count. [Subtree equalities and zero-count theorem](../../../ArkLib/Research/ProximityGap/Frontier/PairedSignatureBalance.lean)

The verifier counts the surviving pairs by subset cardinality and exponent sum modulo $M$. A node of occupancy zero contributes the empty choice. A node of occupancy two contributes zero to the exponent sum modulo $M$. A singleton contributes either $j$ or $-j$. For every possible pair of child occupancies the positive census passes them in their original order and the opposite census passes them in the reverse order. Convolution combines the two child distributions. The subtree equality fixes the difference of the child occupancies, so at most three pairs need checking at each step.

The sum of the entries of a signature is $\sum_{j\in T}\gcd(j,M)$. Each inverse-pair node contributes its occupancy once per descendant leaf, and the number of those leaves is precisely its gcd weight. Rotating a retained subset by $aM/R$ preserves every gcd weight because the reserved subgroup has been removed. Assign each eligible signature sum to **one group of anchors**. At quarter rate the groups are $(0,2),(1)$, and at eighth rate they are $(0,4),(1,5),(2,6),(3)$, indexed from zero in the order shown. A subset cannot be counted in two groups. Within a pair it can be counted twice, and the joint subtree recurrence bounds those repetitions.

For quarter rate, assign a sum $s$ to group $((\lfloor s/d\rfloor\bmod3)\bmod2)$, with $d=3$ for the first prime and $d=1$ for the second. At eighth rate the groups of accepted sums, in anchor-group order, are $\{44\},\{32,48\},\{36\},\{40\}$ on the first prime and $\{44\},\{32,40,46\},\{36\},\{48\}$ on the second. Other sums may be discarded. Each anchor selects its $K$ most populous eligible signed classes from the indicated finite candidate pool. The positive counts exclude all reserved roots. For the overlap upper bound the joint recurrence permits extra roots and both possible signs, retaining only the original product class after rotating the first anchor in the pair to $1$. It counts each signature pair once even when both signs were selected. Subtracting these upper bounds leaves the following populations. [Reproducible counts](../../../scripts/probes/probe_paired_locator_lists.py)

| $M$ | $r$ | Serving fibers | $K$ per anchor | Total before overlap | Repeated subsets at most | Additional agreements |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 1 | 3 | 819 | 1,083,833,129 | 8,986,568 | 20,485 |
| 64 | 1 | 3 | 1,912 | 2,174,783,832 | 26,852,064 | 8,774 |
| 128 | 16 | 7 | 6 | 1,096,999,372 | 381,996 | 1,398,101 |
| 128 | 16 | 7 | 12 | 2,166,459,824 | 1,297,200 | 699,050 |

Run `python3 -O scripts/probes/probe_paired_locator_lists.py`. The script independently enumerates all subsets on quotient orders 8 and 16 and compares every signature pair and product class against the recurrence, including empty classes. The four production populations use the recurrence and the existing finite candidate pools. They provide failing examples. The first failing counts on the named codes still need universal bounds for all centers.
