# Baseline occupancy of dyadic locator lists

At $83,886,079$ agreements on either named length-$2^{30}$ domain, each order-256 degree-nine locator family has at most **1,332,411,487** words in any received ball. Over degrees zero through eight the bounds sum to **48,151,877** on the order-256 quotient and **13,161,160** on the order-128 quotient. On the order-256 quotient the degree-18 cap through eight unpaired roots is **617,033,304**. A separate fixed numerator and multiplier is allowed at each degree. [Named-field fresh-signature census](antipodal-locator-fresh-energy.md)

## Counting root supports inside the baseline coordinates

Let $q$ be the quotient order and $h$ its fiber size. Fix a monic numerator $P$, a nonzero common multiplier $H$ of degree at most $h-1$ and an arbitrary received word. A locator candidate with support $T\subseteq\mu_q$ of size $m$ has polynomial $H(X)Q_T(X^h)$ with $YQ_T(Y)=P(Y)-\prod_{z\in T}(Y-z)$. Each support specifies at most one candidate. Its root product is $(-1)^mP(0)$. Write $r$ for the number of roots of $H$ in the evaluation domain.

Suppose $N$ distinct candidates have at least $t$ agreements each. For a quotient label $y$, let $d_y$ count their supports containing $y$. Let $b_y$ count the coordinates over $y$ where $H$ is nonzero and the center equals the baseline $H(x)P(y)/y$. At those coordinates exactly $d_y$ candidates match. At each of the other $qh-r-\sum_y b_y$ coordinates with $H\ne0$, assume the fresh-signature argument bounds the number matching by $C$. Thus
$$
 N(t-r) \le (qh-r)C+\sum_y b_y(d_y-C)
          \le (qh-r)C+h\sum_{y:d_y>C}(d_y-C).
$$
The last step uses $0\le b_y\le h$ at each label and allows the center to vary within every fiber.

For an arbitrary $s$-element set $S\subseteq\mu_q$, let $j=|T\cap S|$ and $k=m-j$. The number of possible supports in this layer is at most
$$
 B_j(s)=\min\left\{
 \binom{s}{j}\binom{q-s}{k},\quad
 \left\lfloor\frac{\binom{s}{j-1}\binom{q-s}{k}}j\right\rfloor,\quad
 \left\lfloor\frac{\binom{s}{j}\binom{q-s}{k-1}}k\right\rfloor
 \right\}.
$$
Include only layers with $0\le j\le s$ and $0\le k\le q-s$, and omit a quotient with zero denominator. For the second term delete one of the $j$ selected roots. Each set of remaining roots admits at most one completion because the product is prescribed. Deletion outside $S$ gives the third term.

Let $J(N,s)$ be the sum of the $N$ largest entries of the multiset containing $B_j(s)$ copies of $j$ for each layer, padded with zeros if needed. In any such list, $\sum_{y\in S}d_y=\sum_T |T\cap S|\le J(N,s)$. Apply this to $S=\{y:d_y>C\}$. Since $r\le h-1$, every list of size $N>C$ satisfies
$$
 N(t-h+1)\le
 \max_{0\le s\le q}\left\{((q-1-s)h+1)C+hJ(N,s)\right\}.
$$
Here replacing $r$ by $h-1$ increases the right side of the original bound for $Nt$ by $(h-1-r)(N-C)$. The displayed inequality and the total support bound $N\le\lfloor\binom{q}{m-1}/m\rfloor$ for $m>0$ yield computable list caps. The empty support is unique. When $t>(m+1)h-1$, the left side grows by more than $mh$ per added word, while each $J(N,s)$ grows by at most $m$. One may therefore binary-search the first excluded size using exact integers.

## Named-field caps

Set $h=2^{30}/q$ and $t=20\cdot2^{22}-1$. Applying the finite-field signature capacities $C$ gives the following upper bounds for scalar locator lists. Projecting onto any one center component gives the same bounds for lists of repeated scalar words at every interleaving width. [Fresh capacities at the two quotient orders](antipodal-locator-fresh-energy.md#all-root-configurations-at-degrees-zero-through-nine-on-the-order-256-quotient)

| Root degree | Order 128 | Order 256 |
|---:|---:|---:|
| 0 | 1 | 1 |
| 1 | 1 | 1 |
| 2 | 15 | 13 |
| 3 | 37 | 30 |
| 4 | 133 | 96 |
| 5 | 1,489 | 1,788 |
| 6 | 37,788 | 76,662 |
| 7 | 798,924 | 2,645,874 |
| 8 | 12,322,772 | 45,427,412 |
| **Sum through eight** | **13,161,160** | **48,151,877** |
| 9 | | 1,332,411,487 |
| 18, at most eight unpaired roots | | 617,033,304 |

The degree-18 row uses $C=2,830,428$. Its overlap calculation allows every support of the prescribed size and product. The restriction on unpaired roots enters only through $C$. Together with the prime-specific bounds at the remaining classified degrees, these rows cover the second named field's degree-nine branch and the degree-18 branch through eight unpaired roots in one received ball. [Prime-specific union](dyadic-locator-prime-specific-union.md)

The verifier checks all overlap layers at every product on an eight-element group for degrees zero through four. It also compares the excess $\sum_y(d_y-C)_+$ against the layer bound for every subfamily at those degrees, then reproduces the table. [Exact verifier](../../../scripts/probes/probe_locator_baseline_occupancy.py)

```sh
python3 -B scripts/probes/probe_locator_baseline_occupancy.py
```
