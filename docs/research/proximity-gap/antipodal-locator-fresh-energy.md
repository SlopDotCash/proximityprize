# Extra agreements for degree-18 locators with antipodal pairs

At rate $1/16$ on either named length-$2^{30}$ domain, fix a numerator in the order-256 degree-18 locator construction. For **every received word**, at most **670,811,436** candidates whose 18 roots include at most eight unpaired roots reach $20h-1=83,886,079$ agreements, where $h=2^{22}$. This is below both designated list budgets, already at an agreement count below the published over-budget witnesses. Nine-pair families can have more than $2^{30}$ distinct candidates before imposing these additional agreements. The restriction to a received ball is essential here. [Named list witnesses](sixteenth-locator-union.md) · [Higher-degree locator construction and signed-support certificate](dyadic-locator-degree-caps.md)

More generally, fix the set of roots which occur without their antipodes. With two such roots the upper bound is **37,928,532**, and with four it is **4,508,214**. The fixed numerator prescribes the first sum. The named-field four-term sum certificate implies that all orientations having at most four unpaired roots share at most one possibility for that fixed sum. The pure-pair cap of 535,213,545 therefore also covers the union of these three cases. If the prescribed sum is nonzero, the bound for their union is 37,928,532. The five-term certificate below extends these same two bounds through six unpaired roots. Families with ten or more unpaired roots remain outside the result. [Four-term sum certificate](dyadic-locator-degree-caps.md#degree-19-on-the-order-256-quotient)

## The signature of a fresh agreement

Let $D=\mu_{2^{30}}$, let $T\subseteq\mu_{256}$ have size 18, and let $L_T(Y)=\prod_{z\in T}(Y-z)$. The scalar candidates have the form
$$
 f_T(X)=H(X)Q_T(X^h),\qquad Y Q_T(Y)=P(Y)-L_T(Y),
$$
where $P$ is fixed, $H\ne0$ has degree at most $h-1$, and the candidate polynomials meet the dimension bound. In particular $L_T(0)=P(0)$ is fixed. At a coordinate $x$ with $H(x)\ne0$ put $y=x^h$. The baseline value is $H(x)P(y)/y$. If the received value differs from it, a match by $f_T$ prescribes one **nonzero** value of $L_T(y)$. Call such a match fresh. All other matches are over $T$ or at a root of $H$. If $H$ has $r$ distinct roots in $D$, each candidate therefore needs at least $t-18h-r$ fresh matches to reach $t$ agreements. This allows overlaps of locator fibers with roots of $H$.

Fix the unpaired roots $S$. For the remaining $a=(18-|S|)/2$ full pairs let $U\subseteq\mu_{128}$ be their distinct squared roots. Then
$$
 L_T(y)=L_S(y)\prod_{u\in U}(y^2-u),\qquad
 \prod_{z\in T}z=\left(\prod_{s\in S}s\right)(-1)^a\prod_{u\in U}u .
$$
At a fresh match $L_S(y)\ne0$. Set $R=U/y^2$. Then $R$ is an $a$-subset of $K=\mu_{128}\setminus\{1\}$, and both components of its signature
$$
 \sigma(R)=\left(\prod_{z\in R}z,\ \prod_{z\in R}(1-z)\right)
$$
are prescribed. The first is fixed by the numerator, $S$ and $y$. The second is $L_T(y)/(L_S(y)y^{2a})$. Distinct candidates in this fixed orientation give distinct $R$. The normalization works at every one of the 256 quotient values.

## A uniform bound for each nonzero signature

In the finite abelian group $\mu_{128}\times\mathbb F_p^\times$, let $n_j(v)$ count the $j$-subsets of $K$ of signature $v$, let $M_j=\max_v n_j(v)$, and put $E_j=\sum_v n_j(v)^2$. For each of the two named primes the complete exact census is

| $j$ | Subsets | $E_j$ | $M_j$ |
|---:|---:|---:|---:|
| 1 | 127 | 127 | 1 |
| 2 | 8,001 | 8,001 | 1 |
| 3 | 333,375 | 339,637 | 2 |
| 4 | 10,334,625 | 11,202,567 | 6 |

A set of size $a+b$ has $\binom{a+b}{a}$ ordered splits into disjoint sets of respective sizes $a,b$. Their signatures multiply. Counting even the overlapping pairs on the right gives
$$
 \binom{a+b}{a} n_{a+b}(v)
 \le \sum_u n_a(u)n_b(v/u)
 \le \sqrt{E_a E_b}.
$$
The second inequality follows from Cauchy–Schwarz and the permutation $u\mapsto v/u$. Alternatively, first choose any $b$-subset. Its signature fixes that of the $a$-subset, so the right side is at most $\binom{127}{b}M_a$. For the sharper mixed-branch caps, keep the histograms within each of the 128 product classes. For a prescribed target product $c$, a left subset of product $d$ must be paired with a right subset of product $c/d$. At fixed target locator value $v$, the map on nonzero locator values is the permutation $u\mapsto v/u$. The dot product of the two lists of multiplicities is at most their dot product when both lists are sorted in decreasing order, padded with zeros. Indeed swapping any inverted pair increases or preserves the latter sum. Sum these upper bounds over $d$, maximize over the 128 choices of $c$, and divide by $\binom{a+b}{a}$. Taking the minimum with the preceding bounds gives these per-coordinate caps.

| Full pairs $a$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Upper bound $C_a$ on $M_a$ | 1 | 1 | 1 | 2 | 6 | 57 | 1,206 | 19,022 | 160,036 | 2,258,285 |

The five-pair bound also uses the nonuniformity of the four-pair counts. On deleting a singleton from a five-subset, the four-signature is prescribed. Each of the 127 possible singletons contributes a baseline of at most two, plus the positive excess $(n_4-2)_+$. The four-root census has exactly 39,141 signatures of multiplicity at least three. For each such signature and each singleton, multiply their signatures and charge its excess to the resulting product and locator value. The maximum total charge at any resulting signature is **32** on both primes. Dropping the disjointness restriction in this charge can only increase it. Therefore $5M_5\le2\cdot127+32$, giving $M_5\le57$. Deleting a singleton once more gives $M_6\le\lfloor127\cdot57/6\rfloor=1206$. [Exact excess convolution](../../../scripts/probes/probe_antipodal_locator_fresh_energy.cpp)

In particular $M_8\le\lfloor E_4/70\rfloor=160036$ and deleting one root gives $M_9\le\lfloor127\cdot160036/9\rfloor=2258285$. The two prime computations use their actual field elements. [Exact census and small-field control](../../../scripts/probes/probe_antipodal_locator_fresh_energy.cpp)

## Six unpaired roots at the same first sum

Two six-singleton orientations of the prescribed sum that share two signed roots must coincide. Indeed, remove the two shared roots. The remaining two four-term sums are equal, so their non-antipodal supports coincide by the named-field certificate. Each six-singleton orientation thus uses $\binom62=15$ unordered pairs that appear in no other such orientation. The 256 roots have $\binom{256}{2}-128$ unordered non-antipodal pairs, giving at most 2,167 orientations. If a six-singleton orientation exists, no orientation of size zero or two can have the same sum, since their difference would give a reduced nonzero relation of length at most eight after canceling common roots. There may be one four-singleton orientation. Consequently at any fresh coordinate the total number of matching candidates with at most six singletons is at most
$$
 C=\max\{C_9,C_8,C_7,2167 C_6+C_7\}=2,632,424.
$$
This sum permits every nonzero locator value and every center. [Named-field four-term certificate](dyadic-locator-degree-caps.md#degree-19-on-the-order-256-quotient)

## Eight unpaired roots at the same first sum

On each named order-256 subgroup, **every signed zero relation of length at most ten reduces to the empty relation by antipodal cancellation**, including relations with repeated terms. The finite verification extends the four-term sum test. Call a multiset reduced when it contains no pair $z,-z$. For each nonempty reduced multiset of size at most five, modulo common rotation, compute the 256th power of its sum in the prime field. Each result is nonzero and all results are distinct. Indeed, the verifier sorts deterministic 64-bit fingerprints of the full field values and checks that all fingerprints are distinct. Equality in the field would give equal fingerprints. The numbers of representatives at sizes one through five are $1,128,10923,699136,35802317$, respectively, in each field. [Named-field certificate and independent order-16 check](../../../scripts/probes/probe_dyadic_five_term_sums.cpp)

For completeness, if $k$ is the multiset size and $d=\gcd(k,256)$, rotation changes the sum of exponents by a multiple of $k$. Normalize this exponent sum modulo 256 to its unique residue in $[0,d)$. Of the $d$ rotations preserving this normalization, keep the lexicographically least sorted exponent tuple. The first $k-1$ exponents and the normalized product determine the last exponent. Every nonidentity rotation generates a subgroup containing $-1$, so it cannot stabilize a nonempty reduced multiset. Thus the independent expected count is $\frac1{256}\sum_{j=1}^k\binom{128}{j}2^j\binom{k-1}{j-1}$. To deduce the signed relation property, split its terms into two sums of at most five roots, absorbing minus signs into the roots. Cancel antipodal pairs on each side. A nonempty reduced side has nonzero field sum. Two nonempty sides with the same sum must have the same normalized orbit by the certificate, and the same rotation because their sum is nonzero. Thus the two reduced multisets coincide.

For fixed first sum, marking one of six singletons now determines its remaining five. Hence there are at most $\lfloor256/6\rfloor=42$ six-singleton orientations. For eight singletons mark three. They come from distinct antipodal pairs, so there are at most $2^3\binom{128}{3}$ possible marks. Each mark again determines the remaining five. Every orientation supplies $\binom83$ such marks, giving at most **48,768** orientations. Two different weights with sum at most ten cannot coexist at the same first sum, by the signed relation property. If eight occurs, weights zero and two therefore do not occur, and at most one of four and six occurs. If eight does not occur, at most one of zero, two, four and six occurs. Thus the upper bound for the number of matches at one fresh coordinate across all these weights is
$$
 C' = \max\{C_9,C_8,C_7,42 C_6,48768 C_5+\max(C_7,42 C_6)\}=2,830,428.
$$

## Counting the fresh sites across a list

For a fixed orientation let $N_t$ count candidates reaching $t$ agreements about an arbitrary center. Summing their fresh matches first over candidates and then over coordinates gives
$$
 N_t(t-18h-r)\le (256h-r)C_a.
$$
For $t\ge20h-1$, the ratio $(256h-r)/(2h-1-r)$ is increasing for $0\le r\le h-1$. At $r=h-1$ it is $255+1/h$. Since every $C_a<h$, integer rounding gives $N_t\le255C_a$. The pure-pair bound is $255\cdot2258285=575862675$. For the union through eight unpaired roots the same count uses $C'=2830428<h$ at each fresh coordinate, hence $N_t\le255C'=721759140$. Through six, the five-term certificate gives the same cap as the pure-pair case. Fixing a coordinate of an interleaved center yields the same upper bound for the family formed by repeating these scalar words at any positive width.

The same incidence inequality locates the safe side for these low-weight branches more precisely. An over-budget list has $N_t\ge B+1$, so
$$
 t\le 19h-1+\left\lfloor\frac{(255h+1)C_9}{B+1}\right\rfloor.
$$
Indeed $18h+r+(256h-r)C_9/(B+1)$ increases with $r$. For $B=2^{30}$ and $2^{31}$ the last term is respectively $2,249,463$ and $1,124,731$. Thus an over-budget family with at most six unpaired roots would require **at least 991,800,586 and 992,925,318 errors** on the first and second named domains, respectively. Replacing $C_9$ by $C'$ in the same formula gives **991,230,678 and 992,640,364 errors** as the respective lower bounds when up to eight unpaired roots are allowed. These bounds apply to the indicated locator families.

## Accounting for the center's baseline coordinates

On any quotient of order $q$ and fiber size $h$, let $m$ be the locator degree. Fix one numerator, multiplier and received word. Of the $qh-r$ coordinates where $H$ is nonzero, let $b$ be the number where the center equals the baseline $H(x)P(y)/y$. A candidate can match there at most $\min(b,mh)$ times. Only the remaining $qh-r-b$ coordinates can contribute fresh matches. If the family has at most $C$ fresh matches per coordinate, then
$$
 N_t\big(t-r-\min(b,mh)\big)\le(qh-r-b)C.
$$
Suppose $mh+r<t\le qh$. On $b\le mh$ the ratio $(qh-r-b)/(t-r-b)$ increases weakly with $b$, since $qh\ge t$. On $b\ge mh$ its denominator stays fixed and the numerator decreases. The resulting upper bound is its value at $b=mh$. The finite-set theorem `list_capacity` formalizes this incidence step. [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/LocatorAgreementIncidence.lean)

This ratio in turn increases weakly with $r$, giving
$$
 N_t\le\left\lfloor\frac{((q-m-1)h+1)C}{t-(m+1)h+1}\right\rfloor
 \qquad (r\le h-1,\enspace t>(m+1)h-1).
$$

At $q=256$, $m=18$ and $t=20h-1$, each per-coordinate cap above is smaller than $h$, so the bound simplifies to $237C$. Thus at most **670,811,436** words with up to eight unpaired roots reach this agreement, improving the preceding $255C'$ bound. Through six unpaired roots the cap becomes **535,213,545**. For a nonzero prescribed first sum and at most six unpaired roots, the cap is **37,928,532** since the largest possible per-coordinate count is $\max(C_8,C_7,42C_6)=160036$. For an over-budget family the same inequality bounds $t$ by $19h-1+\lfloor(237h+1)C/(B+1)\rfloor$. This also holds when $t\le 19h-1$. The respective error floors for the first and second fields are **991,959,372 and 993,004,711** through six unpaired roots, and **991,429,692 and 992,739,871** through eight.

## All root configurations at degrees zero through nine on the order-256 quotient

For each of the two named fields, every received word has at most **60,855,338** candidates in the union of degrees zero through eight at $20h-1$ agreements, with $h=2^{22}$. Each degree may use a separate fixed monic numerator and nonzero common multiplier of degree at most $h-1$. Every $m$-subset $T\subseteq\mu_{256}$ is eligible. At degree nine alone the bound is **1,786,112,669**, below the second field's $2^{31}$ budget. [Dyadic quotient classification](dyadic-locator-degree-caps.md#locators-on-every-dyadic-quotient-through-order-128)

To see this, retain the whole normalized support $R=T/y$ at a fresh match with $y=x^h$. Here $1\notin R$, and the two components of its signature are $(-1)^mP(0)y^{-m}$ and $L_T(y)y^{-m}$. Both are prescribed and nonzero. For any fixed $x$ the map $T\mapsto R$ is injective. The exact census on $\mu_{256}\setminus\{1\}$ gives the following counts on each prime.

| Size $j$ | Subsets | $E_j$ | $M_j$ |
|---:|---:|---:|---:|
| 1 | 255 | 255 | 1 |
| 2 | 32,385 | 32,385 | 1 |
| 3 | 2,731,135 | 2,757,301 | 2 |
| 4 | 172,061,505 | 179,380,071 | 6 |

There are 330,581 four-root signatures of multiplicity greater than two. Convolving their positive excess $(n_4-2)_+$ with singletons as above gives maximum charge 32. Thus $M_5\le\lfloor(2\cdot255+32)/5\rfloor=108$. The same disjoint-split inequalities and product-class rearrangement on 256 classes give the remaining bounds $C_m\ge M_m$ in the table.

At $t=20h-1$, the baseline-coordinate bound above gives $N_m\le\lfloor((255-m)h+1)C_m/((19-m)h)\rfloor$. The empty support is unique and the prescribed product determines a singleton.

| Degree $m$ | Signature cap $C_m$ | Received-list cap $N_m$ at $20h-1$ |
|---:|---:|---:|
| 0 | 1 | 1 |
| 1 | 1 | 1 |
| 2 | 1 | 14 |
| 3 | 2 | 31 |
| 4 | 6 | 100 |
| 5 | 108 | 1,928 |
| 6 | 4,590 | 87,916 |
| 7 | 155,998 | 3,223,958 |
| 8 | 2,562,572 | 57,541,389 |
| 9 | 72,606,206 | 1,786,112,669 |

## Reproducing the counts

Build the two probes with a C++17 compiler and GMP. The five-term verifier processes the fields sequentially and keeps one 64-bit key per multiset orbit, using less than 300 MB for the keys. The locator verifier defaults to order 128. The optional order-256 run processes the two named fields sequentially. For a fixed product exponent and sorted prefix, the verifier looks up all strictly subsequent root pairs with the required remaining product. It sorts the full reduced locator values, checks the total mass against $\binom{127}{j}$ or $\binom{255}{j}$, and squares the run lengths. An independent enumeration of all $2^{15}$ subsets of $\mathbb F_{17}^{\times}\setminus\{1\}$ checks the small energies and every derived cap through nine roots.

```sh
c++ -O3 -std=c++17 scripts/probes/probe_antipodal_locator_fresh_energy.cpp $(pkg-config --cflags --libs gmpxx) -o /tmp/antipodal-locator-energy
/tmp/antipodal-locator-energy
/tmp/antipodal-locator-energy --order-256
c++ -O3 -std=c++17 scripts/probes/probe_dyadic_five_term_sums.cpp $(pkg-config --cflags --libs gmpxx) -o /tmp/dyadic-five-term-sums
/tmp/dyadic-five-term-sums
```
