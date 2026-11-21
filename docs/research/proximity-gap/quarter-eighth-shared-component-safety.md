# Quarter- and eighth-rate safety from a common component

At the second designated prime the strongest bounds below give first failures at or above **503,316,474** at rate $1/4$ and **662,710,816** at rate $1/8$. The degree-weighted Jacobian argument is in the final section. The first construction gives **498,522,979** and **656,175,519**, respectively, under the following characteristic hypothesis. The following two-row MCA numerator bounds hold on every injective $n$-point evaluation domain over any finite field of characteristic $p>3n^2$.

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

## Reducing the scalar degree cost of the Jacobian columns

At the second prime, the first failing count is at least **503,316,474** at rate one quarter and **662,710,816** at rate one eighth. The same safety estimates apply to any injective domain of this length in characteristic greater than $2^{128}$. This characteristic suffices for the component estimates used here, including the derivative, polar and scalar-degree bounds. On the named subgroup the kernel-checked four-head attacks give the opposite ends of the intervals. [Four-head endpoint theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeFourHeadEndpoints.lean)

| Rate | Last count certified safe here | Upper bound on bad scalars | First-interpolant ordinate and total degrees | Companion ordinate and total degrees |
|---|---:|---:|---:|---:|
| $1/4$ | 503316473 | 2137705552 | 7 and 61782767 | 14 and 52 |
| $1/8$ | 662710815 | 2147480528 | 11 and 223 | 21 and 71 |

Use Hasse multiplicities four and seven for the two interpolants. Their coefficient surpluses are respectively $(164,469800408)$ and $(88248766,426369832)$. The ordinate degree of each primitive common component is $b$, its total scalar-ordinate degree is at most the companion degree $m$, and its weight is $W\le4t-1$. Retain the earlier estimates for the residual resultant, the nonsimple labels, and the large-polar and small-polar cases. The change in the small-polar case is a lower bound on the dimension of polynomial combinations of the Jacobian matrix columns. [Construction of the matrix](second-prime-terminal-cubic.md#a-finite-polynomial-matrix-for-powers-of-the-jacobian-ideal)

Work over the scalar function field and homogenize the ordinate. Write $f$ for the binary component, $U,V$ for the two ordinary polars, and $a$ for the power of their ideal. Pick a constant $\lambda$ so $G=U+\lambda V$ is coprime to $f$ over the coordinate function field. The proper generic polar in the construction ensures this choice. Set $D=2bW-b^2d-b$, $H=2bm-b^2$, and take the ambient binary degree $v\ge ab+b-1$. The ambient coordinate degree is strictly below $L=a(D+W)$. Its dimension is $N_0=(v+1)L$.

First include all columns given by $f$ times a binary monomial of degree $v-b$ and a coordinate monomial of degree below $L-W$. These columns have scalar degree at most $m$ and are independent by cancellation in the polynomial ring. Including more shifts of $f$ than the original matrix allows preserves the specialized divisibility conditions and can only increase the image. There are $N_f=(v-b+1)(L-W)$ columns.

Next take $G^a$ times coordinate monomials of degree below $aD$ and the binary monomials of degree $v-ab$ whose ordinate exponent ranges from zero through $b-1$. These columns lie in the mixed-polar span by the binomial formula and have scalar degree at most $am$. Their number is $N_G=baD$. To see independence modulo the first block, dehomogenize the binary variable. A relation has the form $fA+G^aB=0$ with $\deg_Y B<b$. Coprimality forces $f\mid B$, hence $B=0$ and $A=0$. The bounded monomials in each multiplier are individually independent. [Lean block-independence lemma](../../../ArkLib/Research/ProximityGap/Frontier/PolarBasisDegreeLoss.lean)

Extend these columns to a basis of the enlarged generic image using columns of scalar degree at most $aH$. A column of degree $d_i$ permits a multiplier of degree at most $s-d_i$ inside scalar degree $s$. Independence over the scalar function field implies polynomial independence. The scalar parameter count is therefore $\sum_i(s+1-d_i)$ when all $d_i\le s+1$. In particular the scalar degree cost is at most

$$
  mN_f+amN_G+aH(N_0-N_f-N_G).
$$

This quantity increases with $W,D,v$: the final difference is $baW+(v-b+1)W$. The generic codimension estimate $ag$ continues to hold. Thus the small-polar inequality uses this cost in place of $aHN_0$, with $W$ replaced by its upper bound. For three large noncollinear heads the determinant gives a joint-core sum at most $n+2d$. If three times the minimum large core exceeds this bound, every large triple is collinear and the earlier collinear union estimate applies already to three heads. [Degree-weighted rank calculation](../../../ArkLib/Research/ProximityGap/Frontier/PolarBasisDegreeLoss.lean) · [Three-head determinant](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadDeterminantCover.lean)

The exact-rational certificate checks both interpolation spaces, the two polar estimates at every component degree, the secant recognition test, and all partitions of the common ordinate degree. The largest quarter-rate case has three large heads with common ordinate degree three. The largest eighth-rate case has no large heads and common ordinate degree eleven. The geometry connecting these checks to the MCA statistic is a written proof. [Reproducible certificate](../../../scripts/probes/probe_quarter_eighth_shared_component_safety.py)
