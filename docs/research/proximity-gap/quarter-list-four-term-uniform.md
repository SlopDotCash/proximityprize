# Quarter-rate list decoding at 249/500 agreement

Let $n$ be any positive integer and use any $n$ distinct evaluation points in characteristic zero or prime characteristic $p>\max(50000,1000n)$. Every received word has at most **510,014** Reed–Solomon words of message degree at most $n/4$ agreeing on at least **$249n/500$** sites. The result holds for every positive interleaving width. The corresponding relative error is $251/500$, which exceeds the quarter-rate Johnson radius by $1/500$. At the named length $2^{30}$ on either named prime this caps every list through **539,018,395 errors**. It raises the first-prime first-failure lower bound to **539,018,396**. The second prime has a larger field budget and already has a lower bound of **543,870,915**. [Named benchmark table](full-prize-review.md) The exact worst-center thresholds remain open. [Four-term unit theorem](quarter-list-four-term-units.md) · [Exact length-independent certificate](../../../scripts/probes/probe_quarter_uniform_four_term.py)

## Length-independent interpolation

Set $R=1/4$, $s=249/500$ and use normalized weights $1/n,R,R$ on $X,Y,V$. After scalarization extend the coefficient field to its algebraic closure. For each candidate one may select fractional true hits of total mass exactly $sn$, since a candidate has at least that many true hits. A fractional membership has square at most itself, so the pair-count diagonal corrections used in the variance and slope arguments are unchanged. When counting actual contact with an interpolant below, use all true hits.

Write $S(w,h)=\sum_{0\le j,\,0\le k\le h}(w-(j+k)R)_+$ and use the previously established local rank $C(r,h)$. For a factor of weight $D$ and derivative degree $v$ the normalized quotient threshold is
$$
 Z_v(D;r,h)=\frac{S(rs,h)-S(rs-D,h-v)-C(r,h)+C(r,h-v)}
 {C(r,h-v)-C(r-1,h-v)}.
$$
It is a lower bound on the mean contact order $\mathbb E o$ when the generic degree comparison rules out a second interpolant outside the multiples of the factor. All these formulas work at each actual length. In the difference of the two source dimensions, multiply by a monomial of weight $D$ of the factor: its paired columns have unrounded lengths differing by an integer, so their rounding errors cancel. The unpaired columns have nonnegative rounding error. The finite characteristic assumption covers every derivative exponent in the local rank matrices. [Normalized source and quotient argument](half-list-uniform-length.md#a-source-bound-uniform-in-the-length) · [Quarter-rate normalization](quarter-list-uniform-length.md#the-normalized-interpolation-board)

Use primary order eight and derivative degree two. Its equation has generic total degree at most fifteen. Take $L=250000$ as the stock threshold and $M=260000$ as the forbidden size for a dominant linear factor. Two factors or one irreducible factor of total derivative degree two are tested at order 6000. The smaller linear-factor comparisons also use order 6000. In the remaining interval $5R\le D\le5R+40(2R-s)$ use order 50000 and derivative cap 25000. The remaining factor exclusions are those of the rational midpoint proof with normalized coefficient weights $E=D-R$ and the new quadratic variance bound below. In particular, for a univariate denominator below weight $4R$, $\deg B<3Rn$ while $B$ vanishes at more than $3Rn$ radial sites. The certificate checks the positive primary surplus, both generic degree comparisons, all lower and upper factor-weight intervals, the repeated-root cases and the harmonic invariant using exact rational arithmetic. It treats a shared endpoint with the degree caps of each adjacent interval. [Lower weights and quadratic denominator](quarter-list-rational-midpoint.md#the-quadratic-factor-variance-and-a-quadratic-denominator) · [Radial and coefficient bounds](quarter-first-rational-observable.md)

## Quadratic contact variance

For a quadratic factor or squarefree product $g$ write $c=2+\deg_Y(g_{VV})$, $q=D/R=4D$. Write $p_x$ for the retained words' mean membership and $M_0=L-15^2$. Its variance is at most $\sigma^2=R-s^2+(s-R)/M_0$. The leading coefficient of $g_{VV}$ gives $\mathbb E(o-c)_+\le(q-c)/4$ by the previous proof. Here $2\le c\le q$ and $o\le q+2$.

At an order-zero site the nonzero polynomial $g(x,y_x,V)$ has at most two possible slopes for all hitting words. If $g(x,y_x,V)$ were identically zero, the radial order would be positive. A pair hitting at the same slope costs an extra intersection multiplicity. Summing over ordered pairs and using the slope classes at the order-zero sites gives
$$
 \mathbb E\!\left[p_x^2(1+\tfrac12\mathbf1_{o_x=0})\right]\le R+(2s-R)/M_0 .
$$
Weighted Cauchy–Schwarz with $\mathbb E p_x=s$ then gives $\alpha=\Pr(o_x=0)\le3[1-s^2/(R+(2s-R)/M_0)]\le1/8$. Since
$$
(o-1)^2\le(c-1)(o-1)+(q+1)(o-c)_++c\mathbf1_{o=0},
$$
we get $4\operatorname{Var}(o)\le(c-1)^2+(q+1)(q-c)+4c\alpha$. The right side is convex in $c$. At $c=2$ it is at most $q^2-q$, and at $c=q$ it is at most $(q-1)^2+q/2$. Both are at most $(q-1/2)^2$ for $q\ge2$. Thus the regular-jet comparison uses
$$
\mathbb E o\le1+(D-R)/s+(4D-1/2)\sigma/(2s).
$$
This applies to the squarefree product of two distinct linear factors after the usual generic-jet deletions. [Slope-class diagonal correction](quarter-first-rational-observable.md#slopes-and-orders-below-the-exceptional-weight-interval)

## Contact of an involuted section

In the remaining case let $B$ be the squarefree harmonic quartic, $I_0$ its quadratic invariant, $4BB_{YY}-3B_Y^2=CQ^2$ with primitive quadratic $Q$, $\ell=D-5R$, $I=4R+2\ell$, $K=4D+5E-20R$, and $Z=Z_1(D;50000,25000)$. The absolute degrees of $I_0$ and of the plane resultant are bounded by $nI,nK$. The rational midpoint proof gives the horizontal midpoint from $3Z-(7+K)/2>D+6(R+\ell)$. We next show that the involution $\phi$ sends each other word to a rational solution, retaining the sites of order two as well as those of order three.

Put $c_0=\deg C$. The weight of $Q$ is at most $(3R+\ell)n-c_0/2$ in absolute units. The unreduced denominator of $\phi(f)$ has degree at most $(2R+\ell)n-c_0/2$ and its numerator at most $Rn$ more. At a point with $C(x)\ne0$ and $o\ge2$ the received root is exactly triple: $J=0$ excludes a double root without a triple, and nonzero Hessian excludes a fourth power or zero specialization. Thus $o$ is two or three, $Q(x,Y)$ is a nonzero multiple of $(Y-y_x)^2$, and the projective involution specializes to rank one with image and kernel $y_x$. A true hit of $f$ cancels at least one common zero from the numerator and denominator of $\phi(f)$. This reduces the upper degree of the cleared differential equation by six. At every true miss of $f$ at such a site, $\phi(f)$ instead hits with unit denominator and gives at least $o$ zeros. The original weighted degree bound for that cleared equation is $n[D+6(2R+\ell)]-3c_0$, before cancellations. [Clearing rational sections and commutation](quarter-list-harmonic-involution.md#the-involution-sends-each-polynomial-section-to-a-rational-section)

Allocate these contributions across abscissas and subtract three for each physical true hit of $f$. At a physical site call the residual contribution $m_x$, adding $3\operatorname{ord}_x C$ from the degree gain. Sites of order zero or one have $m_x\ge-3$. At order two $m_x\ge0$; at order three $m_x\ge3$ if $C$ is a unit and $m_x\ge0$ otherwise. Order above three requires $C(x)=0$, so $m_x\ge0$ there. If $o=3$ and $C(x)=0$, the cubic Taylor coefficient vanishes and $I_0$ has order at least two. With $i_x$ the invariant order and $b_x$ the total plane intersection length in that fiber, the individual bounds give
$$
          7m_x+21 i_x+3 b_x\ge39o_x-60 .
$$
The checker verifies each of the seven allowed orders using invariant minima $0,0,1,1,3,4,6$ and intersection minima $(o^2-o-1)_+$. The extra invariant zero in the nonunit order-three case is included explicitly. After restoring at least $3sn$ from the hits, a sufficient interpolation test is therefore
$$
       (39Z-60-21I-3K)/7+3s>D+12R+6\ell .
$$
This proves the involution commutes with the differential equation by the same degree-eleven generic identity and the $M-1$ surviving sections.

The common finite support in the four-term proof has size at most $n[I+K+9-5Z]$. The number of finite places of odd branch-discriminant order is at least $n[Z-1-I]$. The normalized comparison $Z-1-I>8(I+K+9-5Z)$ now contradicts six or more distinct quotient traces, exactly as in the finite proof. It is strict even at the shortest lengths and uses no additive place at infinity because the numerator degree bounds the finite branch places directly. Coarse heights for contact and the Wronskian are below $1000n$, so the stated characteristic hypothesis covers all positive orders to be differentiated. [Good reduction and the four-term unit argument](quarter-list-four-term-units.md)

The checker uses 320 subintervals across the exceptional weights and retains 105 after applying the intersection bounds. It certifies normalized surpluses exceeding **0.066** for the midpoint, **0.021** for the involution, and **0.121** for the branch count. Affine functions minus a positive multiple of $Z$ attain their upper bounds at the interval endpoints by convexity. Nonlinear factors, two large linear groups, and a surviving linear group of size $M$ are thereby excluded, giving the stated total cap $L+M+15-1$.

```sh
python3 scripts/probes/probe_quarter_uniform_four_term.py
```
