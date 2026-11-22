# Extra agreements for degree-18 locators with antipodal pairs

At rate $1/16$ on either named length-$2^{30}$ domain, fix a numerator in the order-256 degree-18 locator construction. For **every received word**, at most **969,664,020** candidates whose 18 roots include at most six unpaired roots reach $20h-1=83,886,079$ agreements, where $h=2^{22}$. This is below both designated list budgets, already at an agreement count below the published over-budget witnesses. Nine-pair families can have more than $2^{30}$ distinct candidates before imposing these additional agreements. The restriction to a received ball is essential here. [Named list witnesses](sixteenth-locator-union.md) · [Higher-degree locator construction and signed-support certificate](dyadic-locator-degree-caps.md)

More generally, fix the set of roots which occur without their antipodes. With two such roots the upper bound is **40,809,180**, and with four it is **4,850,610**. The fixed numerator prescribes the first sum. The named-field four-term sum certificate implies that all orientations having at most four unpaired roots share at most one possibility for that fixed sum. The pure-pair cap of 575,862,675 therefore also covers the union of these three cases. If the prescribed sum is nonzero, the bound for their union is 40,809,180. A separate bound below treats all six-singleton orientations together. Families with eight or more unpaired roots remain outside the result. [Four-term sum certificate](dyadic-locator-degree-caps.md#degree-19-on-the-order-256-quotient)

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
| Upper bound $C_a$ on $M_a$ | 1 | 1 | 1 | 2 | 6 | 98 | 1,746 | 19,022 | 160,036 | 2,258,285 |

In particular $M_8\le\lfloor E_4/70\rfloor=160036$ and deleting one root gives $M_9\le\lfloor127\cdot160036/9\rfloor=2258285$. The two prime computations use their actual field elements. [Exact census and small-field control](../../../scripts/probes/probe_antipodal_locator_fresh_energy.cpp)

## Six unpaired roots at the same first sum

Two six-singleton orientations of the prescribed sum that share two signed roots must coincide. Indeed, remove the two shared roots. The remaining two four-term sums are equal, so their non-antipodal supports coincide by the named-field certificate. Each six-singleton orientation thus uses $\binom62=15$ unordered pairs that appear in no other such orientation. The 256 roots have $\binom{256}{2}-128$ unordered non-antipodal pairs, giving at most 2,167 orientations. If a six-singleton orientation exists, no orientation of size zero or two can have the same sum, since their difference would give a reduced nonzero relation of length at most eight after canceling common roots. There may be one four-singleton orientation. Consequently at any fresh coordinate the total number of matching candidates with at most six singletons is at most
$$
 C=\max\{C_9,C_8,C_7,2167 C_6+C_7\}=3,802,604.
$$
This sum permits every nonzero locator value and every center. [Named-field four-term certificate](dyadic-locator-degree-caps.md#degree-19-on-the-order-256-quotient)

## Counting the fresh sites across a list

For a fixed orientation let $N_t$ count candidates reaching $t$ agreements about an arbitrary center. Summing their fresh matches first over candidates and then over coordinates gives
$$
 N_t(t-18h-r)\le (256h-r)C_a.
$$
For $t\ge20h-1$, the ratio $(256h-r)/(2h-1-r)$ is increasing for $0\le r\le h-1$. At $r=h-1$ it is $255+1/h$. Since every $C_a<h$, integer rounding gives $N_t\le255C_a$. The pure-pair bound is $255\cdot2258285=575862675$. For the union through six unpaired roots the same count uses $C=3802604<h$ at each fresh coordinate, hence $N_t\le255C=969664020$. Fixing a coordinate of an interleaved center yields the same upper bound for the family formed by repeating these scalar words at any positive width.

The same incidence inequality locates the safe side for these low-weight branches more precisely. An over-budget list has $N_t\ge B+1$, so
$$
 t\le 19h-1+\left\lfloor\frac{(255h+1)C_9}{B+1}\right\rfloor.
$$
Indeed $18h+r+(256h-r)C_9/(B+1)$ increases with $r$. For $B=2^{30}$ and $2^{31}$ the last term is respectively $2,249,463$ and $1,124,731$. Thus an over-budget family with at most four unpaired roots would require **at least 991,800,586 and 992,925,318 errors** on the first and second named domains, respectively. Replacing $C_9$ by $C$ in the same formula gives **990,262,299 and 992,156,174 errors** as the respective lower bounds when up to six unpaired roots are allowed. These bounds apply to the indicated locator families.

To reproduce the census, build the probe with a C++17 compiler and GMP, then run it from any directory. For each fixed product exponent modulo 128, it enumerates the prefixes of the sorted subsets and obtains the final root exponent by subtraction. It sorts the full reduced field values of the locator, checks the total mass against $\binom{127}{j}$, and squares the run lengths. An independent enumeration of all $2^{15}$ subsets of $\mathbb F_{17}^{\times}\setminus\{1\}$ checks the small energies and every derived cap through nine roots.

```sh
c++ -O3 -std=c++17 scripts/probes/probe_antipodal_locator_fresh_energy.cpp $(pkg-config --cflags --libs gmpxx) -o /tmp/antipodal-locator-energy
/tmp/antipodal-locator-energy
```
