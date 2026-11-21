# Larger lists on the two named length-$2^{30}$ domains

At security $2^{-128}$, the first named prime permits $2^{30}$ words in a closed list, and the second permits $2^{31}$. At each error count in the table, one center has at least the indicated number of distinct scalar Reed–Solomon codewords. Repeating the row of each word and of the center gives the same conclusion for every positive interleaving width. The six improved upper bounds leave the matching safety estimates for all centers open. [Earlier reciprocal-fiber construction and bounds](reciprocal-fiber-lists.md)

| Named prime | Rate | Previous first-failure upper bound | New upper bound | Distinct words certified |
|---|---:|---:|---:|---:|
| First | $1/2$ | 501,219,329 | **500,520,279** | 1,083,512,160 |
| Second | $1/2$ | 502,118,109 | **502,025,926** | 2,198,117,102 |
| First | $1/4$ | 771,744,959 | **771,742,301** | 1,074,248,723 |
| Second | $1/4$ | 771,749,148 | **771,747,593** | 2,147,920,993 |
| First | $1/8$ | 922,484,737 | **922,365,581** | 1,075,279,395 |
| Second | $1/8$ | 922,611,581 | **922,568,400** | 2,155,690,992 |

## The locator value at the spare fiber

Put $n=2^{30}=Mh$ and $k=(m-1)h$. Write $u$ for a generator of the quotient group of order $M$. For each $m$-subset $T$ of its roots excluding $1,-1$, let $L_T(Y)=\prod_{t\in T}(Y-t)$. If the products of the roots of $T$ are equal, then $c=L_T(0)$ is fixed. The polynomial $Q_T(Y)=(Y^m+c-L_T(Y))/Y$ has degree at most $m-2$. Multiplying $Q_T(X^h)$ by the monic vanisher $H(X)$ of $h-1$ points over $X^h=-1$ gives a codeword of degree at most $k-1$. It agrees with the center $H(X)((X^h)^m+c)/X^h$ over the $m$ fibers in $T$ and at the $h-1$ reserved sites. The monic locators distinguish the codewords. [Lean degree, agreement and allocation lemmas](../../../ArkLib/Research/ProximityGap/Frontier/ReciprocalFiberLists.lean)

To count the unsquared locator values at $1$, represent each selected root as $u^j$ with $1\le j<M$ and retain the sum of these **ordinary representatives modulo $2M$**, denoted $r$. Also retain the leaf vector $v$ in the reciprocal-pair tree. Explicitly the node $j$, $1\le j<M/2$, has occupancy $0$, $1$ or $2$ from the pair $\{u^j,u^{-j}\}$. The tree starts at $M/4$, branches from each even $j$ to $j/2,(M-j)/2$, and stops at odd indices. A leaf entry of $v$ is the sum of the occupancies on its path from the root.

The pair $(v,r)$ fixes $L_T(1)$. To prove this, first take $\zeta=\exp(2\pi i/M)$. For $N(z)=(1-z)(1-z^{-1})$, the identities $N(z)=N(z^{-1})$ and $N(z^2)=N(z)N(-z)$ show that the product of the leaf norms to the powers $v_i$ is $|L_T(1)|^2$ at this complex root. Furthermore $1-\zeta^j=-2i \exp(\pi ij/M)\sin(\pi j/M)$, and the sine is positive for the chosen representatives. The phase of the product depends only on $m$ and $r$. Equality for two sets with the same labels thus holds in the cyclotomic integers. Their integer locator evaluations, viewed as polynomials in $\zeta$, differ by a multiple of $\Phi_M(X)=X^{M/2}+1$. Every primitive $M$th root in either named field is a root of this monic polynomial, so the equality specializes there. In particular $r\bmod M$ also fixes $c$.

## Counting words and agreements

For each retained leaf vector the verifier computes its population by cardinality and by $r$. At a node $j$, the three possible occupancies have exponent shifts $0$, either $j$ or $M-j$, and $M$. Subtract the occupancy from every descendant leaf entry and multiply the two child counts by cyclic convolution modulo $2M$. This counts each subset exactly once. The program selects candidate vectors by perturbing constant vectors on intervals of leaves belonging to subtrees. The pool need only produce enough words. It need not contain every possible vector.

Fix a root product $r_0$ and sort the populations of the individual labels with $r\equiv r_0\bmod M$. Retain $K$ labels with total population above budget. At the spare fiber $X^h=1$, allocate $\lfloor h/K\rfloor$ sites to each retained label and give those sites the value $H(X)(1+c-L_T(1))$ for that label. Every retained word gains at least this many agreements. Other fibers keep their center values, so each word has at least $(m+1)h-1+\lfloor h/K\rfloor$ agreements.

Using one spare fiber gives the following intermediate allocations. The two-anchor construction below improves the half-rate and one-eighth-rate rows.

| Rate | $M,m$ | First prime $(r_0,K,\lfloor h/K\rfloor)$ | Second prime $(r_0,K,\lfloor h/K\rfloor)$ |
|---|---|---|---|
| $1/2$ | $64,33$ | $(4,7,2396745)$ | $(16,14,1198372)$ |
| $1/4$ | $64,17$ | $(1,1741,9636)$ | $(1,3862,4344)$ |
| $1/8$ | $128,17$ | $(16,24,349525)$ | $(0,48,174762)$ |


## Sharing the reserved roots between two fibers

At rates one half and one eighth, every candidate excludes both $1$ and $-1$ from $T$. The $h-1$ common roots of $H$ can occupy any sites in those two fibers. This leaves $h+1$ sites available across both fibers. A locator label served at $1$ receives the same value as above. For a label served at $y=-1$, assign the value $H(x)(y^m+c-L_T(y))/y$ at its sites. A single label of $-T$ fixes $L_T(-1)=(-1)^m L_{-T}(1)$. We use two labels at $1$ and the remaining $K-2$ at $-1$. For $g=\lfloor(h+1)/K\rfloor$, each fiber has space for its assigned $g$ sites per label. Their complement in the two fibers has at least $h-1$ sites, from which we choose the roots of $H$. Every distinct root set served by either fiber gives a word with at least $(m+1)h-1+g$ agreements.

At half rate take $M=64$, $m=33$ and $v_*=(5,\ldots,5)$ on the sixteen leaves. At one-eighth rate take $M=128$, $m=17$ and $v_*=(2,\ldots,2)$ on the thirty-two leaves. At $1$, use both exponent lifts of a chosen root class $r_0$ with signature $v_*$. At $-1$, use both lifts of class $r_0+mM/2\bmod M$ with the same signature of $-T$. Fill the remaining labels at $-1$ with the largest populations whose signature has leaf sum different from that of $v_*$ ($80$ or $64$, respectively). Multiplying the roots by $-1$ exchanges the occupancies of sibling nodes, fixing the root. Siblings have equal numbers of descendant leaves. Consequently the sum of the leaf entries is unchanged by negation, so none of these extra labels can overlap the two labels served at $1$.

The four labels with uniform signature require an intersection count. On each root-to-leaf path the difference between the signatures of $T$ and $-T$ is the sum of the differences between a node's occupancy and its sibling's. The sum of these differences over a pair of sibling nodes is zero. If the two leaf vectors are equal, averaging these path sums over the leaves below a fixed node cancels all contributions of its strict descendants. Thus every path sum down to any node is zero. Taking the difference from the path sum to its parent shows that sibling occupancies must be equal. Conversely, equal sibling occupancies give identical leaf vectors. The verifier imposes this single constraint while counting sets with uniform vector $v_*$. At each sibling pair it takes the same occupancy $0,1$ or $2$ and allows independent orientations for each singleton. It subtracts the resulting root-class count once. Since both lifts at both anchors were selected, this is the exact size of the duplicated family.

| Rate | Named prime | Original root class | Bins at $1,-1$ | Duplicates subtracted | Distinct words | Gain $g$ |
|---|---|---:|---:|---:|---:|---:|
| $1/2$ | First | 8 | 2, 4 | 7,415,224 | 1,083,512,160 | 2,796,202 |
| $1/2$ | Second | 4 | 2, 11 | 7,415,744 | 2,198,117,102 | 1,290,555 |
| $1/8$ | First | 16 | 2, 20 | 143,276 | 1,075,279,395 | 381,300 |
| $1/8$ | Second | 64 | 2, 45 | 143,146 | 2,155,690,992 | 178,481 |

The construction applies on the subgroup and every multiplicative coset by precomposing the evaluation polynomials and the center with a nonzero dilation. The first prime is $365375409332725729550921208179070755120141565953$. The second is $730750818665451459101842416358141509841924915201$.

Run the following command from the repository root. The standard-library verifier first enumerates every allowed subset on quotient orders 8 and 16, checks the predicted label counts against direct enumeration and checks the locator equalities by field arithmetic. It also checks the two-anchor intersection recurrence on three small boards. It then verifies the six single-anchor and four double-anchor production counts, root classes, allocations and budgets. The numerical claims use this integer certificate and the written argument. [Reproduction script](../../../scripts/probes/probe_oriented_fiber_lists.py)

```sh
python3 scripts/probes/probe_oriented_fiber_lists.py
```

## A third fiber for the common vanishing polynomial

At the quarter and eighth rates, remove the ordinary exponent $j=M/4$ from all candidate root sets. The permitted sets already exclude exponents $0,M/2$. Put every one of the $h-1$ common vanishing points on the fiber $X^h=u^j$. This leaves all $h$ positions at each of the two anchors for assigning locator values. If each anchor uses at most $K$ values, every served candidate gains $g=\lfloor h/K\rfloor$ agreements. The quotient has $m=17$, so the distance from the resulting shared center is at most $n-18h+1-g$. [Lean theorem for arbitrary reserved fibers](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean)

| Rate | Budget | Product exponent modulo $M$ | Values per anchor $K$ | Distinct words at least | Extra agreements | First failure at or before |
|---|---:|---:|---:|---:|---:|---:|
| $1/4$ | $2^{30}$ | 1 | 1,123 | 1,074,257,931 | 14,939 | 771,736,998 |
| $1/4$ | $2^{31}$ | 1 | 2,547 | 2,147,852,051 | 6,587 | 771,745,350 |
| $1/8$ | $2^{30}$ | 16 | 14 | 1,147,731,928 | 599,186 | 922,147,695 |
| $1/8$ | $2^{31}$ | 16 | 29 | 2,194,094,160 | 289,262 | 922,457,619 |

The exponent-restricted census at the positive anchor drops the orientation $j$. At the negative anchor it drops $j+M/2$ modulo $M$, the image of the same omitted root under negation. This leaves one available orientation and rules out occupancy two at the corresponding reciprocal pair. Every other reciprocal pair still admits two singleton orientations. The negative-anchor root product is shifted by $mM/2$ modulo $M$, so both count the same original constant.

To count a disjoint union, assign signatures to anchors by the sum $s$ of their leaf entries. Negating a selected set exchanges sibling occupancies at every dyadic depth. Each sibling has the same number of descendant leaves, so the operation preserves $s$. For integers $(d,b)$, serve a set at the positive anchor if bit $\lfloor s/2\rfloor\bmod d$ of $b$ is set and at the negative anchor otherwise. In table order these pairs are $(8,229),(7,90),(4,1),(7,57)$. Within each side retain the $K$ largest permitted populations of signed labels. The two original set families are disjoint, and distinct signed labels within one anchor count disjoint root sets. Their sum therefore counts distinct codewords in one ball. Repeating the scalar center and words gives the result at every positive width.

The exact integer verifier reproduces all four rows. It also checks every five-subset of the ordinary quotient roots for five choices of omitted exponent at order 16 and evaluates all eleven words of a third-fiber example on all 128 sites over $\mathbb F_{257}$. Lean checks the passage from any qualifying family to a single ball. The four numerical restricted-signature counts currently use the integer verifier. [Reproduce the four rows](../../../scripts/probes/probe_third_fiber_lists.py)
