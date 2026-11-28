# The odd-product locator palette at rate one sixteenth

On the first named prime, a closed ball of radius **989,855,734 errors** contains at least **1,084,262,272** codewords. This raises the previously certified list size at the same radius by **8,860,580**. The construction works for every odd exponent of the prescribed product of the nine quotient roots, and row repetition carries it to every positive interleaving width. [Earlier even-product witness](sixteenth-locator-union.md)

On each named prime, the 2,200,000 highest-population signed modes in the odd-product dictionary specified below cover exactly **2,128,536,104** distinct candidate supports across sixteen anchors. This is **18,947,544** below the second-prime list budget. For the received words that retain the baseline on ordinary fibers and use these locator values or the baseline on the remaining fibers, arbitrarily redistributing the reserved sites cannot make more of these candidates gain even one agreement. The two known sixteenth-rate failure ceilings remain 989,855,734 and 989,855,741. [Current witnesses](sixteenth-locator-union.md) · [Exact census and controls](../../../scripts/probes/probe_odd_product_sixteenth.py)

The following smaller prefixes can each be served by a single center giving every represented word at least $10h-1+g$ agreements. Neither of these selections reaches the corresponding named budget.

| Additional agreements $g$ | Modes per anchor | Anchor incidences | Distinct words | Named budget |
|---:|---:|---:|---:|---:|
| 12 | 655,360 | 1,329,541,376 | 985,235,104 | 1,073,741,824 |
| 5 | 1,572,864 | 2,627,858,896 | 1,733,268,568 | 2,147,483,648 |

The smallest ranked prefix whose union exceeds the first-prime budget has **745,183** modes per anchor. The preceding prefix covers 1,073,740,948 candidates and adding that mode raises the count to 1,073,741,956. Allocating ten extra sites per selected mode fits, and the full ten-site allocation of 786,432 modes per anchor certifies 1,112,969,704 words at 989,855,735 errors. This gives a separate odd-product witness one error above the stronger published first-prime ceiling. The prefix ranked by single-anchor population covers 1,044,532,172 words at eleven extra agreements.

## The odd root product and the affine action

Let $M=128$, $n=2^{30}$, $h=n/M$, and $u$ a primitive $M$-th root. Reserve all sixteen fibers $x^h=u^a$ with $a\equiv0\bmod8$. Use ordinary nine-subsets $T$ of the remaining 112 root exponents satisfying $\sum_{j\in T}j\equiv1\bmod128$. The constant coefficient of $L_T(Y)=\prod_{j\in T}(Y-u^j)$ is $-u$. At a reserved anchor the relative signed mode records the reciprocal-tree leaf vector and the sum of ordinary exponent representatives modulo 256. It determines the actual locator value by the signed norm-tree identity. The earlier gain-five upper bound concerned the dictionary for root product one, whose exponent is zero. Here the exponent is one. [Signed locator formula](rotated-locator-union.md#signed-modes-over-the-field) · [Earlier allocation bound](sixteenth-locator-union.md#a-gain-five-upper-bound-for-every-allocation-in-the-signed-dictionary)

For each unit $v\equiv1\bmod8$ define
\[
\phi_v(j)=vj+(1-v)/9\bmod128.
\]
These sixteen permutations form a group and preserve the ordinary grid. They preserve the chosen absolute product because the nine transformed exponents sum to $v+(1-v)=1$. They act simply transitively on the reserved anchors. Indeed, $\phi_{1+8b}(0)=-8b/9$ takes each multiple of eight once. The relative exponents at the image of an anchor are the old relative exponents multiplied by $v$. Multiplication by an odd unit permutes the leaves of the inverse-pair tree. The old signed mode determines the carry in the transformed exponent sum, so the map transports the partition into signed modes. Equivalently, the signed locator identity over a complex primitive root identifies the product of real leaf factors and its phase. Applying the cyclotomic automorphism preserves any resulting equality, which then specializes to the designated prime. The verifier computes every transported mode by applying $\phi_v^{-1}$ to its exponents.

Specify a palette at anchor 0 and transport it to all sixteen fibers. To identify the common dictionary at an arbitrary anchor $a$, choose its unique $\phi_v$ with $\phi_v(0)=a$. On a root set $T$ compute the signed mode of $v^{-1}(T-a)$ at zero. Restrict the dictionary to odd leaf-sum vectors whose unconditioned size-nine population exceeds 6,500. The physical exponents at the canonical anchor have odd sum, hence odd leaf sum. There are 2,958,592 unsigned vectors in this generated pool. The verifier counts the population of each prescribed signed mode at zero and ranks modes by decreasing population. Ties are broken by the packed leaf vector, then the sign bit, in increasing order.

For a prefix of $K$ modes, the total incidence count is sixteen times its single-anchor count. To compute each represented set once, use the smallest canonical rank with which it is represented at any anchor. If that rank occurs at $d$ anchors, give each of those incidences weight $1/d$. Transport by the affine group preserves every rank, so the total weight over all anchors is sixteen times the contribution at zero. The sum counts the exact union. An equivalent census for a fixed prefix gives every incidence weight $1/d$ when $d$ is the total number of represented anchors. The rank assignment computes all prefix unions in one pass.

For the first-prime witness use the full 2,200,000-mode pool to assign each represented root set to its least canonical rank among all its visits. The resulting classes of root sets are disjoint and each class is covered at every site assignment that serves its rank at all anchors. Order these classes by decreasing cardinality, breaking ties by the least canonical rank. The 714,938 largest classes contain **1,084,262,272** root sets in total. Selecting their ranks supports eleven additional agreements per candidate because $714938\cdot11\le h$ and $16\cdot714938\cdot11+h-1\le16h$. The union of this chosen palette may contain additional candidates assigned to other ranks. At twelve extra agreements, the corresponding 655,360 largest classes certify 1,021,595,368 words.

## From the finite count to one received word

Allocate $g$ disjoint sites to each selected signed mode at each of the sixteen anchors. The conditions $Kg\le h$ and $16Kg+h-1\le16h$ leave $h-1$ unused reserved sites for the roots of a common monic $H$. With $Y=X^h$ and $c=-u$, set
\[
 f_T(X)=H(X)\frac{Y^9+c-L_T(Y)}Y .
\]
The numerator has no degree-nine or constant term, so $\deg f_T\le8h-1$. At each evaluation site $x$, let $y=x^h$ and use $H(x)(y^9+c-v)/y$ as its received symbol, where $v$ is the locator value of its assignment, or zero at an unassigned site. Each represented candidate agrees on its $9h$ ordinary root sites, the $h-1$ common sites, and $g$ further assigned sites. These are disjoint, giving at most $n-10h+1-g$ errors. Distinct sets give distinct locators and distinct evaluation words. Repeating the scalar row transports the witness to every positive interleaving width. [Polynomial construction](rotated-locator-union.md#one-center-for-the-selected-sets)

## Why the complete palette bounds every allocation within it

Every candidate agrees with the baseline exactly on the $9h$ ordinary sites over $T$ and the $h-1$ common roots in the reserved fibers. At each other reserved site the received symbol specifies one physical locator value. For two ordinary nine-subsets, equality of their field values at this anchor is equivalent to equality of their signed modes on each of the two primes. The single-anchor unit calculation proves this for every pair of ordinary supports and every fixed product. Equality also survives transport by odd multipliers, since the finite-field equality is equivalent to the complex equality. Thus every positive gain requires membership in the computed union. Powers $j\mapsto bj$ for odd $b$ transport the exponent-one class and its specified palette to every odd absolute product, preserving the count. The result concerns the stated 2,200,000-mode palette and its transported copies. Other signed modes, ordinary-fiber symbol changes, and codewords outside this prescribed family are unrestricted. [Single-anchor equivalence on both named fields](mu128-unit-ellipsoid-transfer.md#single-anchor-locator-values-and-roots-of-unity)

The full palette has **3,393,490,112** incidences. The verifier independently enumerates every eligible ordinary root set at orders 16 and 32. At order 16 it also builds the common roots, all assigned sites, the received word and the represented codewords over the order-128 subgroup of $\mathbb F_{257}$. The production count uses the executable integer census.

```sh
python3 scripts/probes/probe_odd_product_sixteenth.py --workers 3
```
