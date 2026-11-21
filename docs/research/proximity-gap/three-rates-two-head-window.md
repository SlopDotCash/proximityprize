# Exact two-head error curves at three prize rates

Let $16\mid n$, $n\ge2^{30}$, and let $k$ be any integer with $n/16\le k\le n/4$. Write $d=k-1$. Over every finite field of characteristic $p>2n$, for every injective $n$-point evaluation domain, set
\[
 E=\left\lceil\frac{n-k}{2}\right\rceil,\qquad
 T=\left\lfloor\frac{n+3d+4}{3}\right\rfloor+1,\qquad U=n-T.
\]
At every error count $E\le e\le U$ the exact worst-case two-row MCA numerator is **$2(e+1)$**. In particular every integer budget $2E\le B\le2(U+1)+1$ yields first failure $\lfloor B/2\rfloor$ and exact operational radius $\lfloor B/2\rfloor/n$. This extends the earlier two-head ranges at rates $1/4$, $1/8$ and $1/16$ by combining two interpolants. The proof uses only factors of value degree at most two.

| Rate at $n=2^{30}$ | First error count in the exact numerator interval | Last error count | Largest budget in this interval |
|---|---:|---:|---:|
| $1/4$ | 402653184 | 447392426 | 894784855 |
| $1/8$ | 469762048 | 581610154 | 1163220311 |
| $1/16$ | 503316480 | 648719018 | 1297438039 |

## Two interpolation polynomials

For the upper bound suppose $E-1\le e\le U$ and pick $2(e+1)+1$ distinct bad scalar labels, with witnessing polynomials $q_z$ and full agreement sets. Put $t=n-e$ and $\Delta=3t-3d-n\ge5$. We use weights $(1,0,d)$ on $(X,Z,Y)$ and total degree in $(Z,Y)$.

Take a first interpolant of value degree at most two, total degree at most
\[
 h=1+\left\lfloor\frac{n-2d}{\Delta}\right\rfloor
\]
and weight strictly below $t$. The coefficient surplus over the at most $(h+1)n$ received-line constraints is
\[
 (h+1)\Delta-(3t-5d)=h\Delta-(n-2d)>0.
\]
All three allowed value degrees have nonempty coefficient slots since $t\ge n/3+d$ and $d<n/3$. Also $h\ge2$ in this range: $e\ge E-1$ gives $\Delta\le(n-3d+9)/2<n-2d$. This produces a nonzero $Q_1$ containing the selected points $(z,q_z)$ over $\overline{\mathbb F}(X)$.

Independently, take value degree at most four, total degree 16 and weight strictly below $2t$. Impose the identities $Q(x,Z,L_x)=Q_X(x,Z,L_x)=Q_Y(x,Z,L_x)=0$ for all received lines. Their scalar degrees are at most $16,16,15$, giving at most $50n$ constraints. The coefficient surplus is
\[
 150t-140d-50n\ge10d>0,
\]
by $t\ge n/3+d$. At an agreement, $Q(X,z,q_z(X))$ and its derivative vanish, so every agreement counts twice. Its degree below $2t$ forces it to be identically zero. This gives a nonzero $Q_2$ through the same selected points.

## Common factors and the remaining intersections

Take the gcd of $Q_1,Q_2$ in $\overline{\mathbb F}(X)[Z,Y]$, using integral primitive representatives of its irreducible factors. Count labels on all the common components first. Their total value degree is at most two, and each has total $(Z,Y)$-degree at most 16 because it divides $Q_2$. Their product's vertical factors, independent of $Y$, support at most 16 labels. Their monomial weights do not exceed $t-1$, since each divides $Q_1$ integrally after removing coordinate content.

An irreducible quadratic common component has at most 4128 labels. The [quadratic discriminant argument](second-prime-quadratic-discriminant.md#quadratic-fibers-and-the-sylvester-determinant) makes at most $16\cdot34$ exceptions in the coordinate-dependent odd-factor case, using $2t<p$. Otherwise discard at most 34 leading-coefficient exceptions and work on either sign component. From 2048 witnesses discard the at most $t-1-2d$ evaluation sites where the leading coefficient vanishes identically in $Z$. At the other nonidentity sites at most 70 labels agree, giving at least $2d+1-\lceil70n/2048\rceil$ identity sites. The 35 witnesses with fewest misses at these sites each miss a fraction at most $34/2014$. Every three share more than $d$ sites: $(2014-102)(2d-70n/2048)>2014d$ throughout $n/16-1\le d\le n/4-1$. Their 35-point secant would divide the irreducible quadratic. The total cap is $2(2048-1)+34$.

An irreducible common component of value degree one holds at most 184 labels unless it is an actual affine secant. For 185 witnesses the identity set $V$ satisfies $169|V|\ge185t-16n$. At most 15 witnesses miss each identity site by the value-leading coefficient. The 17 witnesses with fewest misses each miss at most $15|V|/169$. Each triple shares at least $124|V|/169>d$ sites, since $124(185(n/3+d)-16n)>169^2 d$. Thus their polynomial points are collinear. The component's restriction to this secant has scalar degree at most 16 and 17 roots. It therefore contains the secant. A genuine secant has occupancy at most $e+1$ by the fresh-site count.

Let $i$ denote the number of distinct actual affine secant factors of the gcd. There are at most two. After dividing the gcd from both interpolants, the residuals are coprime. For $i=0$ or $1$, residual common points with distinct scalar coordinates contribute at most $(4-i)h+32$ labels. Indeed if both residuals have positive value degree, the scalar degree of their nonzero value-resultant is at most the sum of the products of each residual's total degree with the other's value degree, at most $(4-i)h+2\cdot16$. A residual of positive scalar degree alone has at most its own degree in roots; this also satisfies the bound. An everywhere nonzero constant residual contributes none. If $i=2$, the first residual has value degree zero and at most $h$ scalar roots.

Here $3h+8304<e$. To verify it when $\Delta\ge10$, use $3h\le3+3n/10$ and $e\ge3n/8-1$. When $5\le\Delta\le9$, one has $3h\le3+3(n-2d)/5$ and $e=(2n-3d-\Delta)/3\ge2n/3-d-3$. The difference is at least $n/15+d/5-6$. This proves the strict inequality on the complete length range.

When $i=0$, the total population is at most $4h+32+16+2\cdot4128<2(e+1)+1$. For $i=1$ it is at most $e+1+3h+32+16+2\cdot4128<2(e+1)+1$. It follows that $i=2$. Outside the two secants there are at most $h+16$ points since the shared value-degree budget is exhausted. Each of the two secants must consequently have more than $e/3+1$ labels: otherwise the entire population would be at most $(e+1)+(e/3+1)+h+16<2(e+1)+1$.

## Cover and attainment

For a secant containing $L>e/3+1$ witnesses, its joint core has size $c\ge t-2$. Indeed, when $c<t$, the disjoint fresh-site count gives $(L-1)(t-c)\le e$. The two distinct cores intersect in at most $d$ sites. An outside witness agrees on at most $d$ sites of each core and at most $n-2(t-2)+d$ outside their union. Thus it has at most $n-2t+3d+4<t$ agreements, by $\Delta\ge5$. The two heads cover the entire selection, but their cap is $2(e+1)$. This contradiction proves the upper count.

At $E\le e\le U+1$, use two heads $(0,0)$ and $(XH,H)$ with a locator $H$ vanishing at $h_0=\max(0,2(n-e-1)-n)$ common sites. Since $e\ge E$, $h_0\le k-2$. For each head choose $n-e-1-h_0$ disjoint private sites. Its opponent gets one new label $-x$ at each such site. At every remaining site one can prescribe two new distinct labels by solving the two linear equations for the received pair. Choose them outside all the $-x$. There are at most $\max(0,2(e+1)-n)$ remaining sites, and $n+2\max(0,2(e+1)-n)<2n$ in this window. The assumption on the field suffices. Each head's defining sites determine its two row polynomials since $n-e-1\ge k$. Its fresh agreement is nonjoint. These are $2(e+1)$ distinct bad labels, as in the [explicit two-head construction](rate-eighth-two-head-window.md#attainment-and-the-first-failing-count).

Applying the upper bound at the predecessor and the attack at $\lfloor B/2\rfloor$ gives the stated first failure; the real threshold follows from Hamming-step constancy and monotonicity. [Uniform integer certificate](../../../scripts/probes/probe_three_rates_two_head_window.py)
