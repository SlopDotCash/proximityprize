# An eighth-rate list would force 112 million inequivalent split maps

On the first named field, an oversized list at **694,116,763 errors** would give one pair of anchors and **449,965,880 distinct rational functions** of degrees from 86,664,595 to 86,864,594. Each function has three full split fibers on the grid. For each of the three values, its fiber must belong to a prescribed set fixed by the anchors. At least **112,491,470** functions remain distinct up to fractional linear changes of target over the algebraic closure. All these functions are defined over the original grid field, including for a positive-width received word. Excluding or constructing so many maps with a common pair of anchors remains open. [First-prime bounds](full-prize-review.md) · [Exact verifier](../../../scripts/probes/probe_first_eighth_split_neighbors.py)

## Finding one edge with many fully split triangles

Let $n=2^{30}$, $m=n+1$, $d=2^{27}-1$, and $t=379625061$. Via scalar extension take $m$ distinct polynomials over a common extension and choose any $t$ agreement sites $S_i$ for each. Write $s_{ij}=|S_i\cap S_j|$. Distinct words have $s_{ij}\le d$. Join two vertices when $s_{ij}=d$. At a joined pair the polynomial difference is a nonzero scalar times the monic vanisher on its $d$ common sites. In particular it has degree $d$ and no other roots, including after extension.

Writing $mt=nq+b$ with $0\le b<n$, the sum of ordered intersections is at least $nq(q-1)+2bq$. Indeed at a site belonging to $r$ supports the contribution is $r(r-1)$, a convex function of the integer $r$. Each missing ordered edge costs at least one unit of deficit $d-s_{ij}$. The resulting graph has at least $E=410960812476257241$ unordered edges. In any graph with $e$ edges on $m$ vertices, summing the numbers of common neighbors over the edges gives at least
$$
 \sum_i \deg(i)^2-me\ \ge\ 4e^2/m-me.
$$
For an edge $i,j$, its contribution is at least $\deg(i)+\deg(j)-m$ by inclusion-exclusion. Thus there exist joined anchors $a,b$ with at least $\lceil4E/m-m\rceil=457206502$ common neighbors. This part uses the linear incidence bound. Quadratic Hahn inequalities also yield fully split graphs at other errors and budgets. [Hahn inequalities](uniform-cubic-hahn-and-cliques.md)

Write $T=S_a\cap S_b$ and $A=S_a\setminus T$, $B=S_b\setminus T$. For every common neighbor $h$ form
$$
 F_h=(f_h-f_a)/(f_b-f_a).
$$
Put $g=|T\cap S_h|$. The three differences $f_h-f_a$, $f_h-f_b$, $f_b-f_a$ have degree $d$ and split into distinct linear factors. Their common gcd has exactly the $g$ roots $T\cap S_h$. For example, at every root shared by the numerator and denominator the three words take the same value, and the saturated edge $(a,h)$ puts that root in $S_h$. Cancelling the gcd gives three disjoint fibers of size $d-g$, for the target values $0,1,\infty$. The first is contained in $A$, the second in $B$, and the last in $T$. All finite roots are simple. The three reduced members have the same degree, so infinity adds no further point in these fibers.

For $g<d$ these functions descend to the grid field. Write the three uncancelled differences as scalar multiples of monic polynomials $P,Q,D$ belonging to the grid field, respectively in the order $h-a,h-b,b-a$. Normalize all scalars by that of $b-a$. The leading coefficients give $cP-(c-1)Q=D$. The monic $P,Q$ differ when $g<d$, so a nonzero coefficient of $P-Q$ recovers $c$ in the grid field from $c(P-Q)=D-Q$. Distinct neighbors give distinct rational functions, since the fixed denominator polynomial is nonzero.

## Controlling degree for almost every common neighbor

Set $v_i=1_{S_i}-(t/n)\mathbf1$, $a_0=t-d$, and $L=1+m(nd-t^2)/(na_0)$. The matrix with rows $v_i/\sqrt{a_0}$ has Gram matrix $G=I+\epsilon J-D_0$, where $\epsilon=(L-1)/m$ and $D_0$ is the nonnegative symmetric deficit matrix. The upper Rayleigh bound $D_0\preceq I+\epsilon J$ and entrywise nonnegativity imply $\|D_0\|\le L$. It follows that $\|G\|\le 2L$. This bound applies at $m=n+1$ without any lower bound on the fourth trace. Applying the matrix to $1_T-(d/n)\mathbf1$ gives
$$
 \sum_i\left(|T\cap S_i|-dt/n\right)^2
 \le 2a_0 Ld(1-d/n).
$$
This holds for the particular $T$ supplied by the common-neighbor count, regardless of how the anchors were chosen. [Deficit Gram identity](spectral-deficit-list.md)

The map degree $d-g$ has reference value $d(1-t/n)=86{,}764{,}594.728\ldots$. At most $\lfloor2a_0Ld(1-d/n)/H^2\rfloor$ common neighbors lie more than $H$ away. Three choices yield the following simultaneous constraints on the same anchors.

| Half-width $H$ | Maps in the interval | Inequivalent maps | Inequivalent maps at one common degree |
|---:|---:|---:|---:|
| 20,000 | 276,190,944 | 69,047,736 | 1,727 |
| 100,000 | 449,965,880 | 112,491,470 | 563 |
| 1,000,000 | 457,134,096 | 114,283,524 | 58 |

For a fixed nonconstant map of degree $l$, different full fibers are disjoint. Among its target values at most $\lfloor d/l\rfloor$ have a full fiber in $T$, and at most $\lfloor(t-d)/l\rfloor$ have a full fiber in either $A$ or $B$ separately. A change of target is determined by the ordered triple it sends to $\infty,0,1$. Thus at most $\lfloor d/l\rfloor\lfloor(t-d)/l\rfloor^2=4$ maps belong to one equivalence class in the displayed intervals. The last column follows by counting the possible integral degrees.

More generally fix a rational function $V$ of degree $s>0$ over the algebraic closure. For a map $F_h=R\circ V$ of degree $l=rs$ in these intervals, the $r$ poles of $R$ must have full $s$-point fibers in $T$ and its $r$ zeros must have full fibers in $A$. Separability follows here from the full fibers of $F_h$. Choosing the zero and pole divisors of $R$ determines $R$ up to one multiplicative scalar. Different such scalars require disjoint sets of $r$ target values of $V$ above the one fiber in $B$. Hence the number of maps from this one $V$ at that outer degree is at most
$$
 \binom{\lfloor d/s\rfloor}{r}
 \binom{\lfloor(t-d)/s\rfloor}{r}
 \left\lfloor\frac{t-d}{rs}\right\rfloor .
$$
This also handles zero or pole target values at infinity on the intermediate projective line. In the $H=100{,}000$ interval, one $V$ can account for at most **60** of the maps with $\deg R\le2$. Indeed the degree intervals for $s$ when $r=1,2$ are disjoint. At $r=1$ the bound is four. At $r=2$ it is at most $\binom32\binom52\cdot2=60$. Consequently a representation of the retained family by maps of outer degree at most two requires at least **7,499,432** different inner maps up to projective changes of their target.
