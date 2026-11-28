# Quarter-rate list safety on the first prime by rational approximation

At length $n=2^{30}$ on the first named prime, every closed ball through **536,871,004 errors** at rate $1/4$ contains at most $n$ words. The first failing count is at least **536,871,005**. The proof works on any injective grid and at every positive interleaving width. The geometric argument below is written mathematics. The accompanying program checks the integer and rational inequalities. [Exact certificate](../../../scripts/probes/probe_quarter_first_rational_observable.py)

## Reduction to one differential equation

Put $d=n/4-1$, $t=2d-90$, $s=t/n$, $R=d/n$. Scalarize the interleaving over a finite extension and let $k$ be its algebraic closure. Suppose there are $n+1$ distinct degree-at-most-$d$ words with at least $t$ agreements apiece. Use a primary interpolant of order seven, derivative degree at most two and strict weight cutoff $P=7t$, with weights $(1,d,d-1)$ on $(X,Y,V)$. The positive dimension surplus puts every generic word jet $(f,f')$ on one of its factors. Put $b_0=\lfloor(P-1)/(d-1)\rfloor$, $L=\lfloor n/40\rfloor$. Assign each word to one such factor. The factors independent of $V$ account for at most $b_0$ words in total. [Primary and quotient interpolation](sixteenth-list-quotient-jets.md)

For a polynomial $g$ of weight $D$ and derivative degree $v$, let $o_x$ be its order in $u$ after substitution $(X,Y,V)=(x+u,y_x+uz,z+uw)$ with $z,w$ independent. Write $N(W,h)$ for the strict source dimension at weight $W$ and derivative cap $h$, and $C(r,h)$ for the local rank. Define
$$
 Z_{r,h,v}(D)=
 \frac{N(rt,h)-N(rt-D,h-v)-n[C(r,h)-C(r,h-v)]}
      {C(r,h-v)-C(r-1,h-v)} .
$$
If $\sum_x o_x<Z_{r,h,v}(D)$, quotient interpolation yields a secondary interpolant $H$ outside the multiples of $g$ that vanishes on all the generic solution jets in the list. The right side is concave in $D$ because the subtracted source dimension is a sum of positive parts of affine functions. The program checks interval endpoints using the same $r,h$ and the same affine bound on each interval. It computes source sizes at large $r$ by summing the monomial columns in blocks on which $\lceil(W+j)/d\rceil$ is constant. [Quotient criterion](linear-contact-quotient.md#excluding-large-groups-on-high-degree-factors)

A group of size at least $L$ on a quadratic irreducible factor, or two such groups on distinct linear factors, is impossible. In the latter case take $g$ to be the squarefree product. Delete at most $b_0^2$ intersections with $g_V$ from each group, and put $\sigma^2=R-s^2+(s-R)/(L-b_0^2)$. The regular-jet agreement variance bound on the union gives
$$
 \sum_x o_x\le n\left[1+(D-d+1)/t+(D/d+2)\sigma/(2s)\right].
$$
The order-6000 certificate places this strictly below $Z_{6000,h,2}(D)$ for all $2(d-1)\le D<P$. Each group exceeds the product of the two plane degrees, so every factor of $g$ divides $H$, a contradiction. There must therefore be one linear factor $g=A+B V$, $B\ne0$, carrying at least $M=n+1-L-b_0=1,046,898,267$ words. Take $A,B$ coprime in $k[X,Y]$. The case $A=0$ gives $g=V$, whose constant solutions have disjoint agreement sets. For $A\ne0$, every solution has $B(X,f)\ne0$. For any secondary linear-factor comparison it suffices that
$$
 M>\lfloor(rt-1)/d\rfloor+h\max(\deg_Y A,\deg_Y B).
$$
Indeed substitution of $V=-A/B$ in $H$ and clearing $B^h$ gives a polynomial in $Y$ of at most this degree over $k(X)$. The ordinary plane degree product also suffices where the verifier uses it. Consequently the certificate can use $\sum o_x\ge Z_{r,h,1}(D)$.

## Slopes and orders below the exceptional weight interval

Set $E=D-d+1$, $a=\deg_Y B$, $b=\lfloor D/d\rfloor$. The [coefficient intersection estimate](linear-contact-quotient.md#a-contact-order-forces-a-plane-intersection) bounds the sum of the local intersection lengths by $I=aD+bE-dab$. Each length is at least $(o_x^2-o_x-1)_+$. The same bound with $a$ replaced by $\lfloor E/d\rfloor$ holds by monotonicity. In particular
$$
 2j\sum_x o_x\le [j(j+1)+1]n+I\qquad(j\ge2).
$$

Write $U=X-x$, $S=Y-y_x$. Let $m$ be the lesser of the ordinary multiplicities of $A,B$, and $A_m,B_m$ their degree-$m$ homogeneous terms. At least one is nonzero and $m\le b_0$, since $A,B$ cannot both specialize identically to zero at $x$. Call the site radial if $U A_m+S B_m=0$. At any other site, the initial equation $A_m(1,z)+zB_m(1,z)=0$ restricts the slopes of hitting words to at most $b_0+1$ values. At a radial site, $m\ge1$ and $U\mid B_m$, so $B_Y(x,y_x)=0$.

Choose $t$ hits per word and let $p_x$ be the fraction of the group selecting $x$. Two distinct words have at most $d$ common roots counted with multiplicity. A shared hit with the same slope counts twice. At a nonradial site the sum of the squares of the slope-class sizes is at least the square of the hit count divided by $b_0+1$. Counting ordered distinct pairs, the two diagonal corrections together are at most twice the number of hits. With $J$ the nonradial sites this gives
$$
 \mathbb E_x\big[p_x^2(1+\mathbf 1_J/(b_0+1))\big]
 \le R+(2s-R)/M .
$$
Weighted Cauchy–Schwarz and $\mathbb E_x p_x=s$ give $|J|\le n(b_0+2)[1-s^2/(R+(2s-R)/M)]\le5506$. For $a\ge1$ the nonzero $B_Y$ can vanish identically on at most $a-1$ generic words. On any remaining word it vanishes at least $t-|J|$ times, hence $D\ge t+2d-1-|J|$. For $a=0$ and $D<4d-1$ the right side $-A/B$ is polynomial in $Y$ of degree at most three. Its sole possible pole in $Y$ is infinity, and each differentiation increases pole order there by at most two. The isolated-solution count is at most $3+2d$ and the integral-family count is at most $(n-d)/(t-d)$, both below $M$. This follows from the pole and Taylor arguments for a linear equation. [Normalized curve proof](first-order-normalized-curve.md#the-derivative-on-the-smooth-curve)

At every site of order $o\ge1$, $A,B$ have ordinary multiplicity at least $o-1$ and their degree-$(o-1)$ terms satisfy $UA_{o-1}+S B_{o-1}=0$. This follows by taking first the coefficient of $w$ and then the constant coefficient in the defining substitution. In particular $B(x,y_x+S)$ vanishes through degree $o-1$. The leading coefficient of $B$ in $Y$ therefore vanishes in $X$ to order at least $\phi_a(o)=\max(o-a-1,\mathbf 1_{o\ge a+1})$ at $x$. Thus $\sum_x\phi_a(o_x)\le E-ad$.

For $D\le5d-2$ there are four possible denominator degrees. For $a=0$, ordinary multiplicity gives $\sum o_x\le n+E$. For $a=1$, use $o\le1+2\phi_1(o)$, giving $n+2(E-d)$. For $a=2$ use $6o\le11+2\phi_2(o)+(o^2-o-1)_+$, giving $2n+(E-2d)/3+(I-n)/6$. For $a=3$ and $B$ squarefree over $k(X)$ its discriminant is nonzero of $X$-degree at most $4E-6d$ by the homogeneity and index weight of the cubic discriminant. At $o=2,3$ the vertical coefficient vanishing just proved strengthens the usual discriminant order to $1,3$, respectively. At $m=o-1\ge3$ the discriminant order is at least $4m-6\ge2o-3$. Thus $2\sum o_x\le 3n+4E-6d$. [Local discriminant divisibility including the extra order](../../../ArkLib/Research/ProximityGap/Frontier/PrimeHDQuadraticDiscriminant.lean)

A nonsquarefree cubic splits over $k(X)$ into three linear factors counting multiplicity. Write $B$ as its content times their primitive representatives. At a finite zero of a primitive linear factor its $Y$-coefficient is nonzero, by coprimality of its two coefficients. Its initial linear form there cannot be proportional to $U$. Away from roots of the content, the initial form of $B$ is therefore never divisible by $U$. At a radial site $B_m$ is nonzero and divisible by $U$, forcing such a content root. The content has degree at most $E-3d$, fewer than $n-|J|$ throughout this interval. This excludes the remaining cubic. For each of the other possibilities, the certificate uses one of the displayed bounds and $r=6000$ to obtain $\sum o_x<Z_{r,h,1}(D)$. This excludes all weights below $5d-1$.

## The interval from $5d-1$ through $5d+4000$

Take $r=230000000$, $h=\lfloor r/3\rfloor$. The mixed degree bound above holds here. Let $T$ count sites with $o_x\ne3$. The intersection estimate and the lower bound on $\sum o_x$ imply
$$
 T\le\sum_x(o_x-3)^2\le I+10n-5Z_{r,h,1}(D).
$$
At an order-three hit of $f$, $B(X,f)$ has a double zero and $B_{YY}(X,f)$ has a zero. Thus the specialization at $f$ of
$$
 W(X,Y)=(B_{YY})^2/B
$$
has reduced rational height at most $\max(2(D-3d+1),E)-2t+2T$. Here height is the greater degree of the reduced numerator and denominator, with height zero for the zero function. The bounds on $T$ and height are convex in $D$ on each interval of fixed degree caps. The exact endpoint checks give $T\le5571$ and height at most $H=11322$.

If $a=0$, a nonzero univariate $B$ would have a double zero at each of $n-T$ sites, exceeding $E$. If $a=1,2$, its leading coefficient vanishes at all those sites, exceeding its degree $E-ad$. Hence $a=3$ or $4$. If $a=4$ and $B$ has a single distinct geometric root, it is a fourth power of a primitive linear form times its content. The root is rational over $k(X)$ by separability and uniqueness. The content degree is at most $E-4d$. On any word, $B(X,f)$ therefore vanishes to order at least four at each of at least $t-T-(E-4d)$ hits, exceeding its degree $E$.

In every other case $B$ has a root $c$ of multiplicity $\nu$ at which $W$ has pole order $h_0$ with $0<h_0<\nu+1$. For squarefree $B$, choose a root where $B_{YY}$ is nonzero, possible since its degree is $a-2$. Otherwise choose a double or triple root. The order of $B_{YY}$ there is $\nu-2$, giving $h_0=2$ or $1$ respectively. The characteristic is larger than all the degrees involved.

## A determinant for bounded rational height

Work over $K=k(X)$ and set $\delta=\partial_X-(A/B)\partial_Y$. Evaluation at each solution $Y=f(X)$ commutes with this derivation. Put $w_j=\delta^jW/j!$ for $j\le2H+1$. The determinant
$$
 \mathcal D=\det[w_{i+j+1}]_{0\le i,j\le H}
$$
vanishes at each solution. Indeed the coefficients specialize to the Taylor coefficients through degree $2H+1$ of $W(X+u,f(X+u))$. This is rational of numerator and denominator degrees at most $H$ in $u$. Multiplying by its denominator gives zero coefficients at indices $H+1$ through $2H+1$, furnishing a nonzero vector in the kernel.

To see that $\mathcal D$ is a nonzero rational function of $Y$, extend $\partial_X$ to $K^{\rm sep}$, which contains $c$. In the local parameter $y=Y-c$ let $W$ and $\delta y$ have leading terms $w_* y^{-h_0}$ and $v_*y^{-\nu}$. The leading coefficient of $w_j$ at order $-h_0-j(\nu+1)$ is
$$
 w_*[-v_*(\nu+1)]^j (\alpha)_j/j!,\qquad \alpha=h_0/(\nu+1),
$$
by successive differentiation, where $(\alpha)_j$ is the rising factorial. These coefficients are nonzero since the named characteristic exceeds $(2H+2)(\nu+1)+h_0$. All determinant terms have the same candidate leading order. After scaling rows and columns by nonzero constants, its leading coefficient is the shifted Hankel determinant of the coefficients of $(1-u)^{-\alpha}$ through degree $2H+1$.

Here is the nonsingularity argument in positive characteristic. Let $F$ be the truncation of this binomial series through degree $2H+1$, so $(1-u)F'-\alpha F=O(u^{2H+1})$. Singularity would give a nonzero polynomial $Q$ of degree at most $H$ (the reversed kernel coefficients) and a polynomial $P_0$ of degree at most $H$ with $QF-P_0=O(u^{2H+2})$. In particular $P_0\ne0$, since $F(0)=1$. Using the differential equation, the polynomial
$$
 (1-u)(P_0'Q-P_0Q')-\alpha P_0Q
$$
vanishes through degree $2H$. Its degree is at most $2H$, so it is zero. The logarithmic derivative of $P_0/Q$ at $u=1$ gives $\operatorname{ord}_1(P_0/Q)=-\alpha$ in the coefficient field. The integer on the left has absolute value at most $H$. Thus its product with $\nu+1$, plus $h_0$, would be zero modulo the characteristic. That integer has absolute value smaller than the characteristic, and is nonzero since $0<h_0<\nu+1$. This proves nonsingularity.

Finally set $L_0=B\partial_X-A\partial_Y$. Then $\delta^jW=P_j/B^{2j+1}$, with $P_0=B_{YY}^2$ in this recurrence and
$$
 P_{j+1}=B L_0(P_j)-(2j+1)P_j L_0(B).
$$
Here $\deg_Y A\le5$, $\deg_Y B\le4$, so $\deg_Y P_j\le4+8j$. In each determinant term the indices sum to $(H+1)^2$ and the common denominator is $B^{(H+1)(2H+3)}$. The resulting nonzero numerator has degree at most $(H+1)(8H+12)=1,025,727,924<M$. It cannot vanish at all the distinct $f\in K$ assigned to $g$.

For $5d+4001\le D<P$ the coefficient intersection bound alone gives $\sum o_x<Z_{r,h,1}(D)$ and the mixed degree bound. The verifier takes $r=230000000$ below $6d-1$ and $r=6000$ above, splitting wherever either degree cap changes. This exhausts all weights of the dominant factor and proves the closed-ball bound.
