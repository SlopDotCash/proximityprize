# Weighted section variance for three named MCA thresholds

Let $n=2^{30}$. On every injective length-$n$ domain in the second named prime, the first failing MCA error counts are at least **299,100,001** at half rate, **514,400,001** at quarter rate, and **665,600,001** at eighth rate. The bounds apply at every positive interleaving width. They follow from a written geometric proof with the intersection and ramification inputs of the [arbitrary-multiplicity section bound](hodge-section-variance.md). The [exact arithmetic certificate](../../../scripts/probes/probe_weighted_hodge_windows.py) checks the two interpolants, the rich-head thresholds and every factor allocation at each rate.

## Weighting by the fibre degree

Use the preceding bound's notation. In particular, $F$ is an irreducible value-degree-$b$ factor, $b\ge2$, with total scalar/value degree at most $m$ and coordinate/value weight at most $W$. The branch degrees are bounded by $B_X=(2b-2)m-b(b-1)+1$ and $B_Z=(2b-2)W-b(b-1)d+1$. There are $N$ retained simple sections from an original population $M\le N+B_X$. Each has at least $t>d$ agreements on $n$ sites. At site $x$ the truncated divisor $A_x$ has degree $f_x$ between zero and $b$, with $-A_x^2\le mf_x$. Write $I_{zx}$ for its agreement indicator and $\theta_x=N^{-1}\sum_z I_{zx}$. The case $N=0$ is immediate.

Fix a rational $0<K\le1$ with $5\le2K(b+2)$ and $(5K^4-4K^5)t>d$. Then
$$
 M\le B_X+
 \left\lfloor\frac{2K^5 b(4mB_XB_Z+mn+B_XB_Z)+(n-d)(m+1)}
 {(5K^4-4K^5)t-d}\right\rfloor. \tag{1}
$$

Indeed, put $T_x=A_x-(f_x/b)\Phi_X$ and $v_x=T_x\cdot C'_z$ for a retained section. Orthogonality and Hodge index applied to $\sum_{x:f_x>0}(v_x/f_x)T_x$ give
$$\left(\sum_{x:f_x>0}v_x^2/f_x\right)^2\le
c_z\sum_{x:f_x>0} (v_x/f_x)^2(-T_x^2)\le mc_z\sum_{x:f_x>0} v_x^2/f_x.$$
Consequently the weighted sum $\sum b v_x^2/f_x$ over these sites and all sections is at most $4bmB_XB_Z$. On replacing $C'_z\cdot A_x$ by $I_{zx}$, each exceptional pair costs at most $b$ since $f_x\ge1$ is integral. At a zero-degree site all agreements are exceptional since $A_x=0$. Include those sites by charging $b$ per agreement. The two sets of exceptional pairs together have cardinality at most $mn+B_XB_Z$. [Normalized indicator and exception count](hodge-section-variance.md#the-agreement-indicator-on-the-normalized-surface)

For $f_x>0$ write $g=f_x/b$. The mean over sections of the weighted square is $\theta_x/g-2\theta_x+g$. For every $\theta\ge0$, $g,K>0$,
$$
 (5K^4-4K^5)\theta-\theta^3
 \le 2K^5(\theta/g-2\theta+g).
$$
Indeed, with $s=\sqrt\theta$, the right side minus the left is
$$
 s(s-K)^2(s^3+2Ks^2+3K^2s+4K^3)+2K^5(s-g)^2/g.
$$
At $f_x=0$ the same left side is at most $2K^5 b\theta_x$ by the hypothesis on $K$. Summing over sites, use $\sum_x\theta_x\ge t$ and $N\sum_x\theta_x^3\le Nd+(n-d)(m+1)$ from the three-section determinant. This yields (1).

## Joint allocation among linear and nonlinear factors

The following table lists $(r,v,s)$ for each mixed Hasse interpolant, where $r$ is the order, $v$ its maximum value degree and $s$ the total scalar/value degree. Each uses weight below $rt$ and $d=n/\text{rate denominator}-1$. Positive surplus gives both nonzero surfaces containing all selected sections after scalar-only factors are removed. The two surplus values are the monomial counts minus the mixed jet rows.

| Rate | Good errors $e$ | First shape | Second shape | Surpluses | $K$ |
| --- | ---: | --- | --- | --- | --- |
| $1/2$ | 299100000 | $(7,9,31973)$ | $(12,17,109)$ | 87281, 409805125 | $912/1000$ |
| $1/4$ | 514400000 | $(6,11,6594)$ | $(11,22,110)$ | 7237196, 1578414816 | $832/1000$ |
| $1/8$ | 665600000 | $(4,12,1729)$ | $(8,24,85)$ | 3542162, 1238127012 | $757/1000$ |

As in the half-rate proof, assign each chosen scalar to a single irreducible factor of the first surface. Write $(v',a)$ for the value and total scalar/value degrees allowed by the second. Put $L=\max(1+\lfloor e/256\rfloor,1+sv'+va)$. In order down the table these cutoffs are **1,168,360**, **2,009,376**, and **2,600,001**. A factor carrying more than $L$ labels divides the second surface by the scalar-degree bound on its value-resultant. A value-linear factor above this cutoff is an affine head by the identity-site test $t-\lfloor an/L\rfloor-3\lfloor an/(L-a)\rfloor>d$. Each such head carries at most $e+1$ labels and its core has at least $C=t-255$ sites by the disjoint fresh-agreement count. [Common factors and the identity-site test](hodge-section-variance.md#production-specialization)

Let $j$ count the linear factors above $L$, and let $\ell\le v$ be the sum of value degrees of all factors with assigned labels, counted once per factor. For a nonlinear factor of value degree $b$ above $L$, all other factors take at least $(\ell-b)d$ weight on the first surface. On the second surface the $j$ rich affine factors take at least $j$ total scalar/value degrees. Therefore (1) applies with
$$ W=rt-1-(\ell-b)d,\qquad m=a-j. $$
If either bound is below the minimum $bd,b$ for this factor, its population is at most $L$. Otherwise take the larger of $L$ and (1). The characteristic condition $p>\max(b,B_Z)$ holds for the designated prime in every allocation.

At half and quarter rate $3C>n+2d$. Any three noncollinear heads have total core size at most $n+2d$ by their polynomial determinant. At eighth rate $4C>n+4d$, so four heads containing a noncollinear triple cannot all be rich. Thus all $j$ rich heads are collinear whenever $j\ge3$ in the first two rows or $j\ge4$ in the last. [Four-head determinant, including collinear triples](four-arbitrary-head-cap.md#core-multiplicity)

Each pair of distinct cores intersects at most $d$ times. If $U$ is their union and $I$ the sum of their sizes, the site occupancies and Cauchy–Schwarz give $I^2\le |U|(I+j(j-1)d)$. Since $I\ge jC$, this implies $|U|\ge\lceil jC^2/(C+(j-1)d)\rceil$. A covered site gives at most one distinct fresh label across a collinear family and an uncovered site gives at most $j$. Hence the collinear rich-head population is at most $jn-(j-1)|U|$. For all $j$ the independent bound $j(e+1)$ also holds.

For each $j$ enumerate the unordered positive value degrees of the remaining factors, with total at most $v-j$. Every remaining degree-one factor has at most $L$ labels. The three exact maximum populations are **2,128,363,411**, **1,963,198,607**, and **2,137,455,396**, all at most $2n=2,147,483,648$. Respectively, the largest allowed allocations are one degree-nine factor, three large heads plus a degree-eight factor, and three large heads plus a degree-nine factor. The checker examines 284, 618 and 890 allocations. Monotonicity gives every smaller error count and [MCA interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean) gives the width claim.
