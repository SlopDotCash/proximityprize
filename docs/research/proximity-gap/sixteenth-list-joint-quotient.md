# A common second interpolant for the large components

At the second named prime and rate $1/16$, every closed ball through **818,306,368 errors** has at most $2n$ words at length $n=2^{30}$. Thus the first failing error count is at least **818,306,369**. Every injective grid over this field and every positive interleaving width are covered. Here $d=n/16-1$, $t=n/4-13,000,000$, $R=d/n$, and $s=t/n$. [Exact certificate](../../../scripts/probes/probe_sixteenth_list_joint_quotient.py)

Use the [local quotient construction](sixteenth-list-quotient-jets.md) and the [occupancy-dependent orders](sixteenth-list-adaptive-quotient.md). The first-order primary interpolant now uses local order 8 and derivative degree cap 4. Its surplus is 1,361,674,275, its weight is below $8t$ and its total $(Y,V)$ degree is at most $b=\lfloor(8t-1)/(d-1)\rfloor<32$. Assign each of the hypothetical $2n+1$ words to an irreducible factor containing its jet. The factors independent of $V$ cover at most $b$ words. Call a positive-derivative factor large when at least $\lfloor n/25\rfloor$ words are assigned. The small factors cover at most $4\lfloor n/25\rfloor$ words in total.

Let $g$ be the product of the distinct large factors and let $v,D_g$ be its derivative degree and weight. If no factor is large the budget contradiction is immediate. Otherwise $1\le v\le4$. The derivative $g_V$ is relatively prime to every factor of $g$ in $k(X)[Y,V]$ by squarefreeness and the characteristic bound. Remove from each group at most $b^2$ words whose jets lie on both $g,g_V$; these words will still be counted in the final bound on each factor. Each retained group has size $M_j\ge M_0=\lfloor n/25\rfloor-b^2$.

## One assignment of multiplicities for all large groups

Within each group choose exactly $t$ hits per word. Let $p_j(x)$ be its proportion of words selecting site $x$. Choose $p$ in the real convex hull of the $p_j$ to minimize $z=\mathbb E(p-s)^2$, where expectation averages over grid sites. For each $j$, the directional derivative toward $p_j$ is nonnegative. Hence
$$
 \mathbb E[(p_j-s)(p-s)]\ge z .
$$
The one-group variance estimate and convexity give $0\le z\le V_0=R-s^2+(s-R)/M_0$. Since each retained word has nonzero evaluation of $g_V$, convex averaging of the per-group order bounds yields
$$
 \mathbb E (p o_x)\le s+(D_g-d+1)/n,\qquad 0\le o_x\le D_g/d+v .
$$
The latter local order bound also holds for this product: no fiber factor $X-x$ divides it.

Take $r=5000$ and $q_x=\lfloor r+\lambda(p(x)-s)\rfloor$. For every group its mean weighted agreement count is at least $(r-1)t+\lambda n z$ by minimality of $p$. On each individual support $S$, averaging $|S\cap S_i|$ in each group gives $\sum_{x\in S}p_j(x)\le d+(t-d)/M_0$, whether or not $S$ itself belongs to that group. Convexity then gives the individual upper bound $rt+\lambda n V_0$. Use the strict global weight cutoff
$$
                       w=\lfloor (r-3)t+\lambda n z\rfloor .
$$
At least $M_0(2t)/(3t+1+\lambda nV_0)$ words **in every large group** have weighted agreement count at least $w$. This follows by bounding the sum in the group above by $wM_j$ plus the number exceeding the cutoff times the difference between the uniform upper bound and $w$.

## Finite quotient comparisons

Put $B(q)=C(q,h)-C(q,h-v)$ and $J(q)=C(q,h-v)-C(q-1,h-v)$ as in the adaptive proof. Use its two local inequalities with the following rational constants. Write $L=J(r)/s$.

| $v$ | $h$ | $\lambda$ | $b_2$ | $j_2$ | Lower endpoint for $D_g$ |
|---:|---:|---:|---:|---:|---:|
| 1 | 4500 | 17265 | 4.5 | 1.5 | $16(d-1)$ |
| 2 | 1750 | 17344 | 12.1 | 0.7 | $7(d-1)$ |
| 3 | 1750 | 17346 | 18.1 | 0.7 | $5(d-1)$ |
| 4 | 1750 | 17348 | 24.1 | 0.7 | $4(d-1)$ |

The finite check independently verifies the inequalities at every possible multiplicity for these constants. Divide $[0,V_0]$ into 32 equal intervals. On each interval $[z_-,z_+]$ lower-bound the source dimension modulo $g$ by $N(w_-,h)-N(w_--D_g,h-v)$ for $w_-=\lfloor(r-3)t+\lambda n z_-\rfloor$. This quotient dimension is nondecreasing in its weight cutoff by inclusion of filtered spaces modulo the same fixed polynomial. Upper-bound the local cost divided by $n$ by
$$
 B(r)+r/2+b_2r^2 z_++L\big(s+(D_g-d+1)/n\big)
 +(r/2+j_2r^2 z_+)(D_g/d+v).
$$
Within the weight interval from the final table column to $8t-1$ the surplus is concave in $D_g$. The minimum of the integer-rounded lower bounds at the two endpoints across the 32 variance intervals is displayed below.

| $v$ | Minimum surplus | Eligible words on each factor, at least | Upper bound on resultant degree |
|---:|---:|---:|---:|
| 1 | 4,891,524,222,416,866 | 198,975 | 155,651 |
| 2 | 206,727,545,617,014 | 198,075 | 93,818 |
| 3 | 2,687,361,120,123,074 | 198,052 | 114,477 |
| 4 | 5,255,188,366,583,704 | 198,029 | 135,136 |

The quotient produces $H$ not divisible by $g$. Hence at least one large irreducible factor is relatively prime to $H$. For that factor the resultant in $V$ has degree in $Y$ at most $v\lfloor(w-1)/d\rfloor+hb$ by the Sylvester determinant. Every eligible word assigned to that factor is a root in $Y$ of this nonzero resultant. The two right-hand table columns contradict this, excluding all four weight intervals. The use of each group's own weighted agreement lower bound is needed because $g$ can be reducible.

## The remaining counts

The interval for $v=4$ starts at its minimum possible weight and excludes that case. For $v=1,2,3$ the total $(Y,V)$ degree of the squarefree product of large factors is respectively at most $15,6,4$, since weight is at least $(d-1)$ times this degree. If that degree is bounded by $B$, the [normalized differential-curve count](first-order-normalized-curve.md) bounds all words on the large factors, including the discarded singular jets, by
$$
  2Bv-v^2+B+d(4Bv-2B-2v^2)+v(n-d)/(t-d).
$$
In all three cases this number plus $4\lfloor n/25\rfloor+b$ is smaller than $2n+1$. This contradiction completes the written all-center bound.
