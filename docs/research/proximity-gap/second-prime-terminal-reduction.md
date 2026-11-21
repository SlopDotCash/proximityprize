# Reducing the last second-prime predecessor to the low-polar cubic

Fix the second production prime, $n=1073741824$, $d=67108863$, $t=357913943$ and $e=n-t=715827881$. Suppose one received pair has $2n+1$ distinct MCA-bad scalar labels. Choose one polynomial $q_z$ of degree at most $d$ and its witnessing support per label. Write $k$ for the algebraic closure of the prime field. All the selected points $(z,q_z)$ are distinct over $k(X)$. The objective of this reduction is to treat any separate affine head and eliminate every remaining cubic above a specified generic polar threshold.

## Factors and populations

The first-order [quartic interpolation theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuarticInterpolation.lean) gives a nonzero $Q(X,Z,Y)$ of coordinate weight at most $t-1$ for weights $(1,0,d)$, total $(Z,Y)$-degree at most 34 and $Y$-degree at most four. For every selected label $Q(X,z,q_z)=0$. Factor over $k[X,Z,Y]$, removing the content in $k[X]$. All remaining factors are primitive over $k[X]$. The product of the factors independent of $Y$ has degree at most 34 in $Z$ over $k(X)$, so it accounts for at most 34 distinct scalar labels in total.

An irreducible factor of $Y$-degree four has all the remaining positive $Y$-degree and would contain at least $2n+1-34$ selected points. The [terminal irreducible-quartic elimination](second-prime-quartic-intrinsic.md) excludes it.

We recall the smaller-factor counts, including the count when several affine heads coexist. A degree-one-in-$Y$ factor $A(X,Z)Y+B(X,Z)$ holds at most 184 selected points unless it is an affine line over $k(X)$. At each site of the set $U$ where substituting the received line gives an identity in $Z$, at most 33 labels miss it because $A(x,Z)$ is nonzero by primitivity. Outside $U$, at most 34 labels agree. From 185 labels obtain $151|U|\ge185t-34n$. Each of the 35 labels with fewest misses has at most $33|U|/151$ misses. Every three share at least $52|U|/151>d$ agreements, so all 35 lie on a single secant by polynomial interpolation. Restriction of the factor to this secant has scalar degree at most 34, which forces the secant to be a component.

An irreducible factor of $Y$-degree two holds at most 4128 labels by the [quadratic-discriminant reduction](second-prime-quadratic-discriminant.md#quadratic-fibers-and-the-sylvester-determinant). To see the constants, a coordinate-dependent odd-multiplicity discriminant factor permits at most $16\cdot34=544$ exceptions. Otherwise, remove at most 34 leading-coefficient exceptions; the labels lie on at most two sign components. On one component of size 2048, discard the at most $t-1-2d$ sites where the leading coefficient in $Y$ vanishes identically in $Z$. The equality on the sign component defining a remaining nonidentity site allows at most 70 agreeing labels. Its identity set has size at least $2d+1-\lceil70n/2048\rceil=97517567$. Each of the 35 labels with fewest misses has at most $34|U|/2014$ misses there. Every three share strictly more than $d$ sites. The resulting 35-point secant cannot be a component of this irreducible quadratic. Thus at most $2(2048-1)+34=4128$ chosen points lie on it.

For actual affine lines the [two-core incidence bound](second-prime-conditioned-cores.md#at-most-one-186-point-secant-at-the-final-predecessor) gives at most one with 186 selected points. An affine line containing two of the selected points is their actual secant: solving for intercept and slope yields prime-field polynomials of degrees at most $d$. The single-head fresh-site inequality bounds each secant by $e+1=715827882$. There are at most four distinct positive-$Y$ factors, so if they all have $Y$-degree at most two the total number of labels is bounded, generously counting overlaps twice, by
\[
 34+(e+1)+3\cdot185+4\cdot4128<2n.
\]
Thus there is an irreducible $Y$-degree-three factor $F$. Every remaining positive-$Y$ factor uses at least one unit of the sole remaining degree. There can be at most one, with $Y$-degree one and population at most $\max(184,e+1)=e+1$. Together with the parameter-only exceptions this proves that $F$ carries at least
\[
 M=2n+1-34-(e+1)=n+t-34=1431655733.
\]
There is no disjointness assumption and the bound includes the case of a cubic of total value degree exactly three.

## The high polar count

Let $W$ be the coordinate weight of $F$ and $m$ its total $(Z,Y)$-degree. Then $3d\le W$ and $m\le34$. Define $D(h,v)=\sum_{j=0}^h(h-j+1)\max(v-jd,0)$. Take $h=2^{25}$. All total-degree-$h$, weight-below-$t$ interpolants vanishing on all received lines are divisible by $F$ over $k(X)$ by plane Bézout, since $34h<M$. By Gauss's lemma they are integral multiples. Their dimension is at least $D(h,t)-(h+1)n=2251799041933257$. If $W\ge290805099$, the quotient space has capacity at most $D(h-3,t-290805099)=2251799008378920$. Thus $W\le290805098$.

Put $J=W-d$ and let $g_{\rm pol}$ be the generic $X$-degree of the gcd of the two homogeneous polar resultants, after the generic coordinate change in the [persistent singularities proof](second-prime-persistent-singularities.md#local-charges-for-the-two-derivatives). The case with zero second implicit scalar derivative carries at most three labels by the [inverse-derivative argument](second-prime-quartic-intrinsic.md#multiplicities-over-the-scalar-function-field). In the other case put $R=\sum_x r_x$, the sum of local orders at all received lines. Equation (3) of the persistent singularities proof gives
\[
 5R\le 2n+47W-78d-8g_{\rm pol}.
\]
The [finite jet calculation at this predecessor](second-prime-low-genus.md#the-terminal-numbers-with-a-second-head) with $\mu=2048$, $s=470000000$ excludes $R\le C=1073564022$. Explicitly the number of coefficients exceeds the total net cost by at least $387914437758$ there, and the scalar resultant has degree at most $1410000062<M$.

The sufficient polar cutoff is therefore $g_{\rm pol}\ge G(W)$ with
\[
 G(W)=\left\lceil(2n+47W-78d-5C)/8\right\rceil.
\]
For integer $W$ one has $3J-G(W)=\lfloor(5C-2n-23W+54d)/8\rfloor$. This is decreasing in $W$ and equals $19462226$ at $W=290805098$. In particular the high-polar branch $g_{\rm pol}\ge3J-19462226$ is impossible across the full weight range. The complementary case satisfies $3J-g_{\rm pol}\ge19462227$. The threshold's earlier Hamming steps follow from the monotonicity of the repository's actual MCA error function once goodness at this predecessor is established. [Integer checks](../../../scripts/probes/probe_second_prime_terminal_reduction.py)

## Uniform cap when the tested population is $3(e+1)+1$

For $671088640\le e\le715827881$, select $3(e+1)+1$ distinct bad labels to test the upper cap $3(e+1)$. The same fixed interpolation agreement $t_0=357913943$ works for all these data. A slight variant avoids appealing to the earlier 186-point result, whose hypothesis used $2n+1$ selected points.

Suppose all positive-value-degree factors have value degree at most two. With at most two heads carrying more than 512 labels, the total would be at most $2(e+1)+4\cdot4128+34<3(e+1)+1$. Hence there are at least three such heads. Each has core at least $z=356515842$, since the occupancy bound gives $n-e-\lfloor e/512\rfloor\ge z$. Any three noncollinear heads have total core union at least $3z-2d$: their nonzero determinant with rows $(1,A_i,B_i)$ has a root of order at least $j-1$ at a site belonging to $j$ of those cores. An outside point would agree at most $n-3z+5d<t_0$ times. The three heads together hold at most $3(e+1)$ labels, again a contradiction.

Otherwise the $j=3$ or $4$ large heads are collinear in the plane of head pairs over $k(X)$. Their union of cores has size at least $jz-\binom j2d$. At each position outside the union, up to $j$ fresh labels are possible. At each position in the union the evaluated pairs are collinear and contain the received pair. All the other distinct evaluated pairs determine at most one scalar at which they agree with the received fold; heads coinciding with the pair provide no fresh label. Since each selected label on any of the heads needs a fresh site, their total is at most $jn-(j-1)(jz-\binom j2d)$. Adding $4\cdot4128+34$ for every remaining factor is below $3(671088640+1)+1$ for both $j$. Thus some factor has value degree at least three. The quartic elimination's $144903915$-label loss and $268435546$ resultant-degree bound remain sufficient even at the smaller initial population $3(671088640+1)+1$ minus 34. The cubic population is at least $2(e+1)+1-34\ge1342177249$.

The weight calculation is unchanged, since $34\cdot2^{25}<1342177249$. Using $s=440000000$ in place of 470000000, $\mu=2048$ excludes $R\le1073558601$, with strictly positive surplus $694658064894$. The scalar resultant has degree at most $1320000062<1342177249$. For the full interval, the sufficient uniform high-polar cutoff becomes $g_{\rm pol}\ge3J-19458838$. The complementary case therefore gives $3J-g_{\rm pol}\ge19458839$.
