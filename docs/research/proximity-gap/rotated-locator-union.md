# Counting locator lists across rotated anchors

At length $n=2^{30}$ and tolerance $2^{-128}$, each row below gives one closed ball containing more words than the designated field budget. Repeating the scalar center and each scalar word gives the same bound at every positive interleaving width. The indicated error counts bound first failure from above. Matching all-center lower bounds remain open. [Previous witnesses](paired-signature-list-bounds.md) · [Finite verifier](../../../scripts/probes/probe_rotated_locator_union.py)

| Rate | Named prime | Previous ceiling | New ceiling | Distinct words at least | Budget |
|---|---|---:|---:|---:|---:|
| $1/4$ | First | 771,730,931 | **771,728,668** | 1,073,757,956 | 1,073,741,824 |
| $1/4$ | Second | 771,742,624 | **771,741,388** | 2,147,645,137 | 2,147,483,648 |
| $1/8$ | First | 921,278,875 | **921,069,160** | 1,091,906,924 | 1,073,741,824 |
| $1/8$ | Second | 922,039,409 | **921,883,348** | 2,149,615,562 | 2,147,483,648 |

## One center for the selected sets

Write $n=Mh$ with $M=64$ at quarter rate and $M=128$ at eighth rate, so the code has dimension $k=16h$. By scaling the evaluation variable it suffices to work on the multiplicative subgroup. Let $u$ generate the order-$M$ quotient. Reserve the $R=4$ or $R=8$ fibers with quotient exponents $aM/R$ for $0\le a<R$. Every ordinary $17$-subset $T$ in the calculation lies outside these fibers and has one prescribed exponent sum modulo $M$. Thus its monic locator $L_T(Y)=\prod_{j\in T}(Y-u^j)$ has the same constant term $c$ throughout the list.

At each reserved anchor select a collection of signed locator modes, as defined below. Membership in one mode fixes the value of $L_T$ at that anchor. If anchor $a$ serves $K_a$ modes, give each selected mode $g$ disjoint sites over this anchor. With $K=\sum_a K_a$, the conditions
\[
g\max_a K_a\le h,\qquad Kg+h-1\le Rh
\]
leave $h-1$ reserved sites available for the roots of a common monic polynomial $H(X)$. For each $T$ use the message
\[
f_T(X)=H(X)Q_T(X^h),\qquad Q_T(Y)=\frac{Y^{17}+c-L_T(Y)}{Y}.
\]
The leading terms cancel and the numerator vanishes at zero, so $\deg f_T\le(h-1)+15h=k-1$. The locators distinguish the messages. At an unassigned site $x$ use received value $H(x)(y^{17}+c)/y$, where $y=x^h$. At each site assigned to a mode with locator value $v$, use $H(x)(y^{17}+c-v)/y$. A selected set agrees on its $17h$ ordinary sites, at the $h-1$ common roots and at its $g$ assigned sites. These sets of sites are disjoint. This gives at most $n-18h+1-g$ errors. [Polynomial construction](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean) · [Allocation theorem](../../../ArkLib/Research/ProximityGap/Frontier/DistributedAnchorListCensus.lean)

## Signed modes over the field

Relative to anchor $a$, take each ordinary exponent $j$ to $s=(j-aM/R)\bmod M$ in $[0,M)$. The exponents $0,M/2$ are excluded. At the node $i$ for $1\le i<M/2$ store the number of relative exponents in $\{i,M-i\}$. The tree starts at $M/4$. An even node $i$ has children $i/2$ and $(M-i)/2$. Each leaf is odd. Its coordinate $v_\ell$ is the sum of the occupancies along its path from the root. The signed mode is the vector $v$ together with $e=\sum s\bmod 2M$.

To check that the mode determines a field value, choose $z$ of order $2M$ with $z^2=u$ and set $i_0=z^{M/2}$ and $w_j=i_0(z^{-j}-z^j)$. A quadratic extension suffices for this identity if necessary. Then $1-u^j=-i_0 z^j w_j$, $w_{M-j}=w_j$ and $w_{2j}=w_jw_{M/2-j}$. Multiplication down the tree gives
\[
 L_T(u^{aM/R})=(u^{aM/R})^{17}(-i_0)^{17} z^e \prod_{\ell\ \mathrm{leaf}}w_\ell^{v_\ell}.
\]
Its left side belongs to the original field. Distinct modes may give the same field value without affecting the assignment proof. The verifier checks the singleton factorization on both named primes. Consequently these four combinatorial bounds also hold for any smooth coset of the same order whose field budget is smaller than the corresponding word count. [Single-anchor count and norm identities](oriented-fiber-list-bounds.md)

## Pair intersections for arbitrary anchor rotations

Let $C_a$ be the collection of ordinary $17$-sets whose relative signed mode is selected at anchor $a$. For $a<b$, measure exponents from $a$ and set $d=(b-a)M/R$. The two inverse-pair matchings now pair $j$ with $-j$ and with $2d-j$ modulo $M$. Both reflections preserve the ordinary grid. They have no fixed point there, since all their fixed points are reserved. Their orbits have at most $R$ sites. Indeed, composing the reflections rotates by $2d$, whose order divides $R/2$.

For each signature the verifier enumerates all possible occupancies of the inverse pairs. At a node with inherited path counts already removed, choose $0$, $1$ or $2$ occupants up to the smallest residual leaf value. Force the occupancy to zero if the pair is reserved. Subtract the choice from the descendant leaf values and recurse independently on the two children. A leaf must use its entire residual. Retaining total weight $17$ gives every possible occupancy vector exactly once.

Given one such vector for each anchor, restrict to one orbit of the two matchings. Direct enumeration of the orbit's at most $2^8$ subsets gives every assignment realizing both sets of edge occupancies. An occupancy of zero or two determines both endpoints. When the occupancy is one, either endpoint determines the other. Propagation through the connected orbit gives at most two assignments. Keep the two relative sums of ordinary exponent representatives for each assignment. Combining independent orbits and testing both sums modulo $2M$ counts exactly the subsets belonging to both selected signed modes.

As an index for this count, the program groups occupation vectors by the number selected in each orbit and the total of the leaf coordinates. For any $j$ its contribution to the latter total is $\gcd(j,M)$. Since every ordinary $j$ has smaller 2-adic valuation than $M/R$, adding a multiple of $M/R$ preserves this contribution. Both indexing quantities therefore agree for every actual intersection. The program verifies all local edge constraints after the lookup. Distinct signed modes within an anchor are disjoint as labels of root sets, so adding over their pairs gives $|C_a\cap C_b|$. [Cycle enumeration](../../../scripts/probes/probe_rotated_locator_union.cpp)

Every set represented at $z\ge1$ anchors contributes $z-\binom z2\le1$ to the sum of singles minus pairs. This gives the following lower bounds on the union. The verifier constructs the candidate modes with the existing signed norm-tree recurrence, selects them in decreasing order of population under both the per-anchor cap and the total cap, and recomputes all $\binom R2$ intersections. The product column gives the common exponent sum modulo $M$.

| Rate | Budget | Product | Total modes | $g$ | Single-anchor incidences | Pairwise intersections | Union at least |
|---|---:|---:|---:|---:|---:|---:|---:|
| $1/4$ | $2^{30}$ | 12 | 2,163 | 23,269 | 1,090,462,734 | 16,704,778 | 1,073,757,956 |
| $1/4$ | $2^{31}$ | 15 | 4,771 | 10,549 | 2,167,292,585 | 19,647,448 | 2,147,645,137 |
| $1/8$ | $2^{30}$ | 8 | 34 | 1,677,721 | 1,092,217,628 | 310,704 | 1,091,906,924 |
| $1/8$ | $2^{31}$ | 8 | 68 | 863,533 | 2,151,345,320 | 1,729,758 | 2,149,615,562 |

The scalar polynomial and fiber allocation implications use the linked Lean results. The displayed populations are exact-integer computations. Reproduce the certificate with Python 3 and a C++20 compiler. Its controls enumerate root sets directly at orders 8, 16 and 32, compare each pair count for three different choices of the modes, and evaluate a shared center and its selected polynomial words at every point of a length-128 domain over $\mathbb F_{257}$.

```sh
python3 scripts/probes/probe_rotated_locator_union.py
```
