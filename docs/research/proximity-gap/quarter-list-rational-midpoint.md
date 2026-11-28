# First-prime quarter-rate safety from the rational midpoint

On the first named prime, every closed quarter-rate ball of radius **538,870,914 errors** contains at most $n=2^{30}$ Reed–Solomon words, for every injective grid of this length and every positive interleaving width. The first failing count is at least **538,870,915**. This improves the earlier safe count by 550,000. The proof uses scalarization and the established quotient interpolation inequalities. The geometry below is written mathematics and the finite comparisons use exact rational arithmetic. [Earlier logarithmic bound](quarter-list-harmonic-logarithm.md) · [Executable certificate](../../../scripts/probes/probe_quarter_first_rational_observable.py)

Put $d=n/4-1$, $t=2d-2000000$, and let $k$ be the algebraic closure of the scalarized coefficient field. A primary interpolant of radial order eight, derivative degree at most two, and weight strictly below $8t$ has positive surplus. Let $b_0=\lfloor(8t-1)/(d-1)\rfloor$ and take large-group threshold $L=2000000$. The preceding factor reduction, with the following two estimates, puts at least $M=n+1-L-b_0=1071741810$ distinct polynomial sections on one irreducible equation $g=A+BV$. Write $D$ for its weight, $E=D-d+1$ for the bound on $B$, and $o_x$ for its local radial order. The weights of $X,Y,V$ are $1,d,d-1$. [Factor and contact reduction](quarter-first-rational-observable.md)

## The quadratic-factor variance and a quadratic denominator

For the intermediate derivative-degree-two equation $g$ (one irreducible factor or a squarefree product of two), write $C=g_{VV}/2$, $a=\deg_Y C$, $c=a+2$ and $q=(D+2)/d$. The coefficient of $V^2$ has weight at most $D-2(d-1)$, so $2\le c\le q$. At a site of radial order $o$, differentiating twice in the local derivative variable $w$ shows $C(x+U,y+Uz)$ is divisible by $U^{o-2}$ when $o\ge2$. Each coefficient of the polynomial in $z$ therefore has the same divisibility. Its leading ordinate coefficient vanishes in $X$ to order at least $(o-c)_+$. Its degree is at most $d(q-c)$. Hence the average of $(o_x-c)_+$ is at most $(q-c)/4$, since $n=4d+4$.

The general radial bound gives $0\le o_x\le D/d+2\le q+2$. The inequality $o^2\le co+(q+2)(o-c)_+$ gives
$$
\operatorname{Var}(o_x)\le c^2/4+(q+2)(q-c)/4\le q^2/4
$$
by $(c-2)(c-q)\le0$. If $s=t/n$ and $\sigma$ bounds the standard deviation of the chosen hit proportions, the usual covariance argument now gives $\sum o_x\le n[1+(D-d+1)/t+q\sigma/(2s)]$. The checker uses this estimate in the order-50,000 quadratic comparison, with the Bézout cap rechecked at the stated $L$. [Regular-jet variance and the covariance inequality](sixteenth-list-quotient-jets.md)

For a linear equation with squarefree quadratic denominator $B=b_2S^2+b_1S+b_0$, $S=Y-y$, the discriminant $b_1^2-4b_2b_0$ has $X$-degree at most $2E-2d$. At contact order two the valuations of $b_0,b_1$ are positive. At order three the valuations of $b_0,b_1,b_2$ are at least $2,1,1$. At higher order $o-1$ ordinary multiplicity gives discriminant valuation at least $2o-4$. Thus $\sum o_x\le n+2E-2d$. For a repeated quadratic, write $B=C_0(X)L_0(X,Y)^2$ with $L_0$ primitive linear. Away from the roots of its content, the initial form of $B$ cannot be divisible by $U=X-x$: if $L_0(x,y)=0$, its $Y$-coefficient at that point is nonzero. A radial site, as defined in the factor reduction, requires a nonzero initial form of $B$ divisible by $U$. In this weight interval $\deg C_0\le E-2d<2d$, whereas the number of radial sites exceeds $2d$. This excludes the repeated quadratic. The other lower and upper weight comparisons use the existing bounds with the new parameters.

## Interpolation of the midpoint

In the remaining weight interval $5d-1\le D\le5d+80000000$, set $l=D-5d+1$, $E=4d+l$ and let $Z=Z_{r,h,1}(D)$ with $r=180000000$, $h=r/2$. The quotient estimate forces $\sum o_x\ge Z$. As in the preceding harmonic reduction, the exact weight comparisons force the binary quartic invariant $J$ to vanish and exclude all cases except a squarefree quartic $B$ in the affine ordinate. The coordinate at infinity is fixed throughout the following argument. The Hessian has the form
$$
4BB_{YY}-3B_Y^2=C(X)Q(X,Y)^2,\qquad Q=q_2Y^2+q_1Y+q_0
$$
with $Q$ primitive. Write $c_0=\deg C$. Since the Hessian has weight at most $2E-2d$, one has $\operatorname{wt}(Q)\le3d+l-c_0/2$. The original good-site estimate supplies a site with a triple finite root and different fourth root. In particular $q_2$ is nonzero. [Quartic case exclusions and Hessian](quarter-list-harmonic-involution.md) · [Per-weight invariant orders and good-site estimate](quarter-list-harmonic-logarithm.md#the-stronger-endpoint-at-538320914-errors)

In lowest terms put $m=S_0/T_0=-q_1/(2q_2)$ and let $u=\max(\deg T_0,\deg S_0-d)$, treating the zero numerator as degree $-\infty$. Then $u\le d+l-c_0/2$. At every site with $o_x\ge2$ and $C(x)\ne0$, the specialized $B$ has the finite received ordinate as a root of multiplicity at least two. A double root without a triple root contradicts $J=0$. A fourth power or a zero form would have zero Hessian, whereas $C(x)Q(x,Y)^2\ne0$ by primitivity. Thus there is a triple received root and a different fourth root, possibly at infinity. Its Hessian is a nonzero fourth power of the received linear form. It follows that $q_2(x)T_0(x)\ne0$ and $m(x)$ equals the received ordinate.

The cleared equation $T_0^6g(X,m,m')$ has degree at most $D+6u$. At every such site the radial substitution gives contact at least $o_x$, including for a rational section with unit denominator. Define $v(o)=\min(o,3)-\mathbf 1_{o=1}$. The total contact is at least $\sum v(o_x)-3c_0$, since only the roots of $C$ can lose a positive term and each costs at most three. For orders $0\le o\le6$ direct substitution gives
$$
2v(o)\ge6o-7-(o^2-o-1)_+.
$$
If $R$ is the coefficient intersection bound for the actual ordinate degree caps, total contact is consequently at least $3Z-(7n+R)/2-3c_0$. The certificate checks
$$
3Z-(7n+R)/2>D+6(d+l).
$$
The content contribution cancels on the two sides. The cleared equation is identically zero, so $m$ is a rational solution.

## The common finite support

Use the primitive linear polynomial $P=T_0Y-S_0$. For any polynomial solution $f\ne m$, every finite zero of $P(X,f)$ is a zero of $B(X,f)$. At such a zero $T_0$ is a unit and $f=m$. If $B(X,f)$ were a unit there, both sections would satisfy the same regular local equation $Y'=-A/B$. Their right-hand sides differ by a multiple of $f-m$. An order $j>0$ of $f-m$ would give order $j-1$ on differentiating since $j\le\deg(T_0f-S_0)\le d+u<p$. This is impossible. All zeros of $B(X,f)$ also give intersections of $A,B$ because $f$ is a solution.

At an order-three site where $B$ specializes with a triple received root and different fourth root, suppose the full intersection length in the fiber is five. At this site $m$ is regular and hits. Both quadratic initial forms are as in the preceding local proof, $B_2=U(aU+cV)$ and $A_2=-V(aU+cV)$ with $V=Y-y$. They cannot both be zero because ordinary multiplicities at least three would give length at least nine. For any regular horizontal section through the point, of slope $v$, the number $a+cv$ is nonzero. If $c=0$ this follows from $a\ne0$. If $c\ne0$ and $a+cv=0$, the factorization $A+f'B=(Y-f)H$ used in the earlier proof gives intersection length at least six. The same local argument applies to the rational regular graph $m$. Consequently $B$ has order exactly two on every hitting section. [Local length computation](quarter-list-harmonic-logarithm.md#a-fixed-exceptional-set)

Two distinct hitting solutions have different slopes here. Put $V=Uz$, $A=U^2a_1(U,z)$, $B=U^2b_1(U,z)$ after substitution. The initial forms give $a_1+zb_1=Uc_1$, so the transformed differential equation is $c_1+b_1 z'=0$. At every hitting slope $v$ we have $b_1(0,v)=a+cv\ne0$. If $f$ and $m$ had the same slope, their transformed sections would have finite positive contact of order at most $d+u-1<p$, contradicting the preceding regular-equation argument. It follows that $P(X,f)$ vanishes simply on each hit. On a miss another zero of $B(X,f)$ would be a second intersection in the same fiber. Therefore $W_f=B(X,f)/P(X,f)^2$ is a unit at every such site.

Use $I_0$ for the quadratic invariant of $B$, with $\deg I_0\le4d+2l$. At a grid point of order $o$, reserve $i(o)$ zeros of $I_0$ and $b(o)=(o^2-o-1)_+$ intersection length, with $i(0),\ldots,i(6)=0,0,1,1,3,4,6$. At an order-three point that uses exactly the two reserved quantities (one and five), $b_3(x)\ne0$ because $b_3(x)=0$ would give invariant order at least two. This is a clean site as above. At a different order with positive reserve, charge the site once. With zero reserve any zero or pole of $W_f$ costs an unreserved intersection. The same holds at every other finite abscissa. The total intersection bound is $R_0=4D+5E-20d$. Using $i(o)+b(o)-\mathbf 1_{o\ne3,\ i(o)+b(o)>0}\ge5o-9$ gives a common finite support of size at most
$$
 s_*=(4d+2l)+R_0+9n-5Z.
$$
The primitive denominator introduces no additional leading-coefficient zeros. As $m$ solves the equation, $P$ divides $(B\partial_X-A\partial_Y)P$ over $k(X)$. The logarithmic-derivative argument for $B/P^2$ therefore gives a nonzero polynomial of ordinate degree at most $8(\lfloor s_*\rfloor+1)$ vanishing on at least $M-1$ surviving words. [Derivative recurrence and nonvanishing](quarter-list-harmonic-logarithm.md#a-differential-equation-with-too-many-distinct-roots)

The verifier splits the exceptional weights at degree-cap changes and at multiples of $2000000/8$ above $5d$. Of 322 intervals it excludes 217 by the intersection bounds and checks the last estimates at both endpoints of the remaining 105. Each lower comparison is concave, since $Z$ is concave within the chosen interval. Each upper bound is convex. The worst support bound is **106,567,523**, the minimum midpoint interpolation surplus is **86,720,086**, and the uniform ordinate degree cap is **852,540,192**. The required $M-1=1071741809$ distinct roots exceed the cap. These checks exclude an over-budget center, completing the stated bound. The exact first failing error count remains open.

Run the previous cases and the two-million certificate together from the repository root.

```sh
python3 scripts/probes/probe_quarter_first_rational_observable.py
```
