# Larger lists on the two named length-$2^{30}$ domains

At security $2^{-128}$, the first named prime permits $2^{30}$ words in a closed list, and the second permits $2^{31}$. At each error count in the table, one center has at least the indicated number of distinct scalar Reed–Solomon codewords. Repeating the row of each word and of the center gives the same conclusion for every positive interleaving width. The six improved upper bounds leave the matching safety estimates for all centers open. [Earlier reciprocal-fiber construction and bounds](reciprocal-fiber-lists.md)

| Named prime | Rate | Previous first-failure upper bound | New upper bound | Distinct words certified |
|---|---:|---:|---:|---:|
| First | $1/2$ | 501,219,329 | **500,520,279** | 1,083,512,160 |
| Second | $1/2$ | 502,118,109 | **502,025,926** | 2,198,117,102 |
| First | $1/4$ | 771,744,959 | **771,742,301** | 1,074,248,723 |
| Second | $1/4$ | 771,749,148 | **771,747,593** | 2,147,920,993 |
| First | $1/8$ | 922,365,581 | **922,101,604** | 1,077,692,870 |
| Second | $1/8$ | 922,568,400 | **922,447,288** | 2,197,233,550 |

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

## A third fiber for the common roots at rate one eighth

Take $M=128$, $m=17$, $h=2^{23}$ and root class $16$. After the anchor labels have been chosen, each member $T$ of the candidate family misses exactly $109$ of the $126$ quotient nodes other than $1,-1$. Counting pairs $(T,z)$ with $z$ missed shows that some ordinary fiber $z$ is missed by at least $\lceil109N/126\rceil$ of the $N$ candidates. Keep these candidates and put all $h-1$ roots of $H$ in that fiber. Both anchors now have all $h$ sites available. The $17$ fibers in each retained $T$ still contribute $17h$ agreements. The common zeros and the assigned anchor sites raise this to $18h-1+g$. The Lean theorem takes the population before restriction, finds the fiber and proves a strict lower bound on the canonical worst-center list. [Formal construction and averaging proof](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean)

Start both anchor pools with the two exponent lifts of the uniform vector $(2,\ldots,2)$. These four classes overlap in exactly $143276$ candidates as above. Each additional group in the table specifies a leaf sum $W$, an anchor, and a number of labels. At each group take that many largest label populations at the indicated weight and anchor from the verifier’s finite signature pool. At $1$ the exponent representatives lie over $16$ modulo $128$. At $-1$ the corresponding representatives of $-T$ lie over $80$. Negation preserves the leaf sum, so groups with distinct weights are disjoint even across anchors. No added group has the uniform weight $64$. Within each group the labels partition the candidates, including when two labels give the same field value.

| Prime | Additional groups $(W,\text{anchor},\text{labels})$ | Labels per anchor | Distinct candidates $N$ | Retained at least | Gain $g$ |
|---|---|---:|---:|---:|---:|
| First | $(48,+1,4),(68,-1,11),(60,+1,7)$ | 13 | 1,245,773,409 | 1,077,692,870 | 645,277 |
| Second | $(48,+1,4),(68,+1,16),(60,-1,16),(66,-1,10),(72,+1,6)$ | 28 | 2,539,921,351 | 2,197,233,550 | 299,593 |

With $K$ labels at each anchor, each receives $g=\lfloor h/K\rfloor$ sites. Each retained word has at least $18h-1+g$ agreements with the same center. The resulting list exceeds $2^{30}$ words on the first prime at **922,101,604 errors** and $2^{31}$ on the second at **922,447,288 errors**. The integer recurrence supplies the two candidate populations and the explicit error counts. Exact first failure at either prime still requires a matching all-center safety bound. [Population verifier](../../../scripts/probes/probe_oriented_fiber_lists.py)

The construction applies on the subgroup and every multiplicative coset by precomposing the evaluation polynomials and the center with a nonzero dilation. The first prime is $365375409332725729550921208179070755120141565953$. The second is $730750818665451459101842416358141509841924915201$.

Run the following command from the repository root. The standard-library verifier enumerates every allowed subset on quotient orders 8 and 16, checks the predicted label counts against direct enumeration and checks the locator equalities by field arithmetic. It also checks the two-anchor intersection recurrence on three small boards. It checks six single-anchor counts, four counts with the common roots at the two anchors, and both third-fiber counts, together with their root classes, allocations and budgets. The numerical claims use this integer certificate and the written argument. [Reproduction script](../../../scripts/probes/probe_oriented_fiber_lists.py)

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

## Three and seven serving fibers

Reserve the full subgroup of quotient exponents $0,M/d,\ldots,(d-1)M/d$, with $d=4$ at quarter rate and $d=8$ at eighth rate. Use the last fiber for the $h-1$ common zeros and each of the other $d-1$ fibers to serve locator values. The original candidate sets of size 17 avoid the whole reserved subgroup. Their common root product fixes the same polynomial constant $c$ as in the two-anchor construction.

| Rate | Budget | Serving fibers | Values per serving fiber | Distinct words at least | Extra agreements | First failure at or before |
|---|---:|---:|---:|---:|---:|---:|
| $1/4$ | $2^{30}$ | 3 | 887 | 1,073,797,722 | 18,914 | **771,733,023** |
| $1/4$ | $2^{31}$ | 3 | 2,524 | 2,147,776,086 | 6,647 | **771,745,290** |
| $1/8$ | $2^{30}$ | 7 | 8 | 1,193,754,620 | 1,048,576 | **921,698,305** |
| $1/8$ | $2^{31}$ | 7 | 17 | 2,161,068,386 | 493,447 | **922,253,434** |

For each candidate set of exponents $T$ put $s(T)=\sum_{j\in T}\gcd(j,M)$. Its ordinary signature has this leaf sum because a node at exponent $j$ has $\gcd(j,M)$ odd descendants. Every member lies outside the reserved subgroup, so its 2-adic valuation is strictly below that of $M/d$. Adding a multiple of $M/d$ preserves both its valuation and $s(T)$. Assign a set to serving anchor index $(\lfloor s(T)/t\rfloor+b)\bmod(d-1)$, with $(b,t)=(0,3),(0,1),(4,3),(4,3)$ in table order. Each original set has exactly one assigned anchor.

Write $y=u^{aM/d}$ for the quotient root at serving anchor $a$. Translating all original exponents by $-aM/d$ preserves the excluded subgroup and gives the locator identity $L_T(y)=y^{17}L_{T/y}(1)$. Thus the existing signed labels at $1$ give one actual locator value at $y$. The integer verifier fixes original product exponent 1 at quarter rate and 16 at eighth rate. For anchor $a$, it reads the two signed exponent lifts of the rotated product class $r-17aM/d$ modulo $M$, accepting only the assigned sums. Summing the largest allowed signed-label populations on each serving fiber counts disjoint original sets. A fiber with at most $K$ allocated values supplies $\lfloor h/K\rfloor$ agreements, on top of the $17h$ ordinary agreements and the $h-1$ common roots.

Lean constructs one center for arbitrary serving palettes and proves the distinct-word list bound from the common constant, the root sets and the fiber capacities. The exact integer verifier checks the four production populations. At quotient order 16 it also exhausts the restricted histograms and evaluates the resulting degree-bounded words and common centers on all 128 coordinates over $\mathbb F_{257}$. [General allocation and locator theorem](../../../ArkLib/Research/ProximityGap/Frontier/TwoAnchorListWitness.lean) · [Production and finite checks](../../../scripts/probes/probe_serving_subgroup_lists.py)

## Can the full-field shifted-cube lists reach the first open step?

On the two named subgroups $H=\mu_n\subset\mathbb F_p^\times$, $n=2^{30}$, the first
unresolved closed ball at each of the four rates requires an agreement count $T=n-e$
satisfying both $3T>4k$ and $T\ge268{,}435{,}453$. Here $k$ is the code dimension and
$e$ is one more than the last proved safe error count. At rate $1/8$ the second prime
has one more proved safe error than the first. [Four-rate safety](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListJohnsonRank.lean) · [Extra safe step](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListJohnsonPuncture.lean)

Alrabiah, Goyal and Guruswami construct large lists over the full prime field.
Take a subgroup $S=\mu_t$, with $t\mid p-1$, and a polynomial $f$ with $f(0)=0$
and degree $2\le d<t$. Put $P_f(X)=\prod_{u\in S}(X-f(u))$. Their coefficient
bound gives $\deg(X^t-P_f)\le t-\lceil t/d\rceil$. For $\ell\ge1$ such maps,
the received word is $X^{\ell t}$ and the message is $X^{\ell t}-\prod_i P_{f_i}$.
Its agreements on $H$ form the union of the sets $f_i(S)\cap H$.
The published degree bound certifies membership in the dimension-$k$ code when
$\ell t-\lceil t/d\rceil+1\le k$. The paper uses shifted cubes
$f_a(X)=(X+a)^3-a^3$ in its prime-field examples. [Section 4, Lemmas 4.1–4.3 and amplification](https://arxiv.org/html/2611.07607v1#S4)

The construction needs $T\le\ell t$. The certified degree condition gives
$k>\ell t-t/d$, so $\ell t<k\ell d/(\ell d-1)$. If $\ell d\ge4$, this
allows fewer than $4k/3$ agreements even before restricting the evaluation set.
The remaining cases have $\ell=1$, $d=2$ or $3$, and $t<2k\le n$.

For a nonmonomial $f$ in either remaining case, its graph $y=f(x)$ in the
two-dimensional torus is absolutely irreducible of bidegree $(d,1)$. Over the
algebraic closure its smooth completion is the projective line. Removing infinity
and the distinct roots of $f$ gives the torus graph. Thus its Euler
characteristic in the convention of Corvaja and Zannier is
$\chi=\#\{\text{distinct roots of }f\}-1$, with $1\le\chi\le d-1$.
At a nonzero root of $f$, the valuation of $x$ is zero and the valuation of
$f(x)$ is positive. This excludes a relation $x^i f(x)^j=\mathrm{constant}$
for $(i,j)\ne(0,0)$, as required to exclude a translate of a subtorus.
Corollary 2 gives
\[
 |f(\mu_t)\cap\mu_n|\le
 |\{u\in\mu_t:f(u)\in\mu_n\}|\le
 \max\left\{3(2tnd\chi)^{1/3},\,12tnd/p\right\}.
\]
Both primes exceed $2^{158}$. The second term is less than one, and the cube of
the first is at most $324n^2<7{,}201{,}920^3$. Thus even a single nonmonomial
has at most **7,201,919** agreements on the required domain. [Corvaja–Zannier, Corollary 2, p. 1930](https://ems.press/content/serial-article-files/31918#page=4)

For a monomial $f(X)=cX^d$ injective on the seed, the image is $c\mu_t$ and
$X^t-P_f=c^t$ is constant. At most $\lfloor n/T\rfloor$ constants can have $T$
agreements with a fixed word, since their agreement sets are disjoint. These
counts rule out the published degree certificate as a witness at all eight
first unresolved steps. A proof of extra coefficient cancellation, including
after reduction modulo $X^n-1$, could certify other parameter choices. Linear maps $f(X)=cX$ allow a separate count that includes different seed sizes giving the same center. When $\ell\ge2$, the degree certificate gives $\ell t\le2(k-1)<n$, and $T>4k/3$ forces $\ell\le3$. The center $X^{\ell t}$ determines its exponent uniquely on $H$ in this range. Hence at most one $t$ occurs for each $\ell=2,3$. A coset of $\mu_t$ intersects $H$ in zero or $g=\gcd(n,t)$ sites. All selected cosets must be distinct and meet $H$, since $(\ell-1)t<T$. Then $g\ge T/\ell$, and the number $n/g$ of eligible cosets is a power of two strictly below 13, hence at most eight. Even across both amplifications there are at most $\binom82+\binom83=84$ messages at this center. Unamplified monomials injective on the seed give at most four agreeing constants, including when their center exponents coincide modulo $n$. A noninjective monomial has at most $t/2<k<T$ image points in the remaining unamplified degree-two and degree-three cases. The combined bound of 88 is below both budgets.

The obstruction is a written application of the two papers. Safety at the eight closed balls remains open.
