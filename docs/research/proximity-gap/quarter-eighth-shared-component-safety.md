# Quarter- and eighth-rate safety from a common component

For the second designated prime at $n=2^{30}$, the first failing error count at rate $1/4$ is at least **498,522,979**, and at rate $1/8$ it is at least **656,175,519**. The following two-row MCA numerator bounds hold on every injective $n$-point evaluation domain over any finite field of characteristic $p>3n^2$.

| Dimension | Safe errors $e$ | Agreements $t=n-e$ | Maximum bad labels |
|---|---:|---:|---:|
| $n/4$ | 498522978 | 575218846 | 2139423135 |
| $n/8$ | 656175518 | 417566306 | 2144204508 |

Both maxima are below the second-prime budget $2n=2147483648$. This improves the previous written rate-eighth first-failure floor by 119,264 errors. The previous uniform two-head window at rate one quarter reached 447,392,426 safe errors. The proof here uses written geometric component estimates and an exact-arithmetic certificate. [Rate-eighth estimates](rate-eighth-eight-degree-safety.md) · [Two-head window](three-rates-two-head-window.md) · [Certificate](../../../scripts/probes/probe_quarter_eighth_shared_component_safety.py)

## Removing the intersections outside the common component

Put $d=k-1$. For the multiplicity-three interpolant use ordinate degree $b_0$ and total scalar-ordinate degree $h$. For the multiplicity-six companion use degrees $b_1,m$.

| Rate | $b_0$ | $h$ | $b_1$ | $m$ | Surpluses |
|---|---:|---:|---:|---:|---:|
| $1/4$ | 6 | 28150537 | 12 | 41 | 49 and 843689810 |
| $1/8$ | 8 | 11711847 | 18 | 51 | 364 and 1566081803 |

The surplus counts all coefficient slots of weight below $3t$ or $6t$, then subtracts the corresponding received-line Hasse jet conditions. Both interpolants contain every selected scalar and polynomial-witness pair.

Over the coordinate function field, let $C$ be the gcd of the two interpolants in the scalar and ordinate variables. Write them $CA,CB$ and put $c=\deg_Y C$. Since the total degree of $C$ is at least $c$, the coordinate-field $Y$-resultant of $A,B$ has scalar degree at most

$$
 E_c=(b_0-c)(m-c)+(b_1-c)(h-c).
$$

The resultant at the actual ordinate degrees is nonzero since the residual factors are coprime over the scalar function field. At a common scalar specialization with an ordinate witness and $C$ nonvanishing, the resultant vanishes, including where one input loses degree. If both residuals have ordinate degree zero, their coprimality in the scalar polynomial ring excludes common roots directly. Thus at most $E_c$ labels lie outside $C$. Its scalar-only factors contribute at most $m$ labels. The remaining distinct factors have total ordinate degree at most $c$, individual total scalar-ordinate degree at most $m$, and coordinate weight $W\le W_*=3t-1$ in their primitive integral representatives. The latter bound follows from weight additivity and divisibility of the first interpolant.

## The populations of the common factors

Apply the [normalized-Hessian and Jacobian-power estimates](rate-eighth-eight-degree-safety.md#interpolation-and-the-component-estimates) to each component of ordinate degree $b\ge2$. Replace the split parameter in that proof by $\eta=(W^2/(2d)+\beta n)/a$ for positive rational $\beta$. In the high-polar case subtract $(2+8\beta/a)n$ in the quadratic lower bound for $5(tW/d-R)$. In the low-polar case $a\eta-W^2/(2d)=\beta n$, so the exact dimension inequality becomes $(s+1)\beta n>aH(v+1)a(D_*+W_*)$. All other terms are unchanged, with the chosen scalar bound $m$ replacing 63. The certificate lists every $\beta,a,\mu,s$ and minimizes the high-polar quadratic on the full component-weight interval. It also checks the 4096-witness secant test for value-linear factors.

The resulting degree-by-degree caps for $b=2,3,\ldots,b_0$ are

| Rate | Component caps in order of increasing $b$ |
|---|---|
| $1/4$ | 6562468, 15712468, 58564977, 265694977, 1970519908 |
| $1/8$ | 9261192, 13520298, 25041192, 55440596, 128440596, 340590596, 901441192 |

A genuine head is large when its selected population exceeds $L=\lfloor e/512\rfloor+1$. Each such head has at least $T=t-511$ joint-core positions. The test $4T>n+4d$ holds at both rates, so any four large heads are collinear by the four-head incidence inequality. If $j\ge4$ large heads occur, their combined label count is at most

$$
 jn-(j-1)\left\lceil\frac{jT^2}{T+(j-1)d}\right\rceil .
$$

For $j\le3$ use $j(e+1)$. Every other value-linear component has at most $L$ labels. For each $0\le j\le c\le b_0$, allocate the other $c-j$ ordinate slots to the degree-indexed caps above and to $L$ for degree one. Add the $j$-head contribution, $E_c$, and $m$. The largest totals are the bounds in the first table. At rate one quarter the largest case has $c=6,j=0$. At rate one eighth it has $c=3,j=3$. [Four-head incidence](four-arbitrary-head-cap.md) · [Exact finite calculation](../../../scripts/probes/probe_quarter_eighth_shared_component_safety.py)
