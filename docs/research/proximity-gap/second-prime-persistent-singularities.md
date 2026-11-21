# Persistent singularities of a cubic carrying many polynomial sections

At the second production prime, length $n=2^{30}$ and degree bound $d=2^{26}-1$, the code on any $n$ distinct field elements has at most $2n$ MCA-bad scalars at **694616142 errors**. Its first bad error count is therefore at least **694616143**. The proof uses two generic first derivatives to detect singularities that persist as the scalar $Z$ varies. Their intersections consume part of the degree previously allocated to the received points by the normalized Hessian.

## A lower bound for the persistent intersections

Let $k$ be the algebraic closure of the prime field. As in the [previous argument](second-prime-normalized-hessian.md), take a primitive irreducible $F\in k[X,Z,Y]$ of $Y$-degree $b=3$, total $(Z,Y)$-degree at most $m$, and weight $W$ for the weights $(1,0,d)$ of $(X,Z,Y)$. Suppose $M$ distinct labels $z$ supply polynomial sections $F(X,z,q_z(X))=0$ with $\deg q_z\le d$. Among these, at least $M_1=M-(5m-6)$ have $F_Y(X,z,q_z(X))\ne0$. Indeed the nonzero resultant of $F,F_Y$ over $k(X)$ has $Z$-degree at most $(b-1)m+b(m-1)-b(b-1)=5m-9$ by the Sylvester index sum.

Make a single fractional linear change $X\mapsto\phi(X)$ with denominator $h(X)$ and multiply $Y$-coefficient $c_j(\phi(X),Z)$ by $h(X)^{W-jd}$. Thus each section becomes $h(X)^d q_z(\phi(X))$. The weights and the two degree bounds persist, as does primitivity since some coefficient attains its weight. Choose the old coordinate $r=\phi(\infty)$ away from the domain, the zeros of all the nonzero section derivatives $F_Y(X,z,q_z(X))$, and the finitely many $r$ for which $F(r,Z,Y)$ fails to have three simple, nonzero, finite roots over $\overline{k(Z)}$. The last condition follows from separability, nonzero constant coefficient and nonzero leading coefficient of $F$ in $Y$. At a transformed evaluation site the received line acquires the same constant factor as its section.

The derivative along each of the $M_1$ sections, in the new chart, now has $X$-degree exactly $J=W-d$: its leading coefficient is a nonzero constant times the original $F_Y(r,z,q_z(r))$. Write $F_z=(Y-q_z)G_z$. Then $G_z(q_z)=F_Y(X,z,q_z)$ has degree $J$, even if the degree of $q_z$ is below $d$.

For an indeterminate $\lambda$ define the homogeneous $Y$-resultant
\[
 P_\lambda(X,Z)=\operatorname{Res}_{Y}^{3,3}(F,F_X+\lambda F_Y).
\]
It has $Z$-degree at most $H_p=6m-9$ and $X$-degree at most $D=6W-9d-3$ by the same Sylvester index sum. In this chart the $X$-degree is exactly $D$. Indeed the initial form at $Y=X^d U$, after dividing by $X^W$, is a cubic $f(U)$ with three simple nonzero roots, by the choice of $r$. The corresponding initial form of $F_X+\lambda F_Y$ after division by $X^{W-1}$ is $Wf-dUf'$, since $d>1$. It is nonzero at every root of $f$. Thus the top coefficient of the resultant is nonzero.

In each of the $M_1$ fibers $G_z(q_z)^2$ divides $P_\lambda(X,z)$. The first product factor, from $Y-q_z$, equals $(\lambda-q_z')G_z(q_z)$. Modulo $G_z$, the second polynomial in the resultant is $(Y-q_z)((G_z)_X+\lambda(G_z)_Y)$, giving the other factor of $G_z(q_z)$. These identities hold with the indicated homogeneous degrees, so an additional degree drop can only contribute a leading factor or a zero resultant.

Take independent $\lambda_1,\lambda_2$ and let $g$ be the generic $X$-gcd degree of the two polars $P_{\lambda_i}$. The generic rank of the degree-$D$ Sylvester matrix is $2D-g$. In every selected simple fiber its rank is at most $2D-2J$. A nonzero generic minor of size $2D-g$ has $Z$-degree at most $(2D-g)H_p$. At each selected fiber it vanishes to order at least $2J-g$ if this is positive, by rank loss over the local DVR. Consequently, for $M_1>H_p$,
\[
 g\ \ge\ 2J-\left\lfloor\frac{(2D-2J)H_p}{M_1-H_p}\right\rfloor . \tag{1}
\]

## Local charges for the two derivatives

The $X$-gcd counts fixed intersections over $k(Z)$, with no $X$-infinity contribution because both polars have exact degree $D$. Indeed the gcd is the content in $X$ common to all $\lambda$ coefficients of $P_\lambda$: after removing it, any root of the first polar cannot annihilate the second, since $\lambda_2$ is independent over the field containing that root and $\lambda_1$. At a fixed finite $X$ place use local resultants or the determinant on the normalization to sum branch orders. The generic value of a linear combination on a branch has valuation the minimum of the two orders, by transcendence of $\lambda$. Denote that order by $\nu$; their sum across the projective $Y$ fibers is $g$. For instance, the resultant valuation on a monic chart equals the order of a norm, which sums these orders with residue degrees. After the separable constant extension below the relevant residue degrees are one.

Work over the separable closure of $k(Z)$ so that differentiation in $Z$ extends. All relevant finite $X$ centers are separable since their degree is at most $D<p$. Above them the local fields of the normalization have degree at most three over the completed $X$-line on each component. They are tame, with trivial residue extension. Each branch consequently has a parameter $t$ with $X=\alpha+t^e$, $1\le e\le3$. One can obtain this parameter by taking an $e$th root of the unit multiplying a uniformizer to its $e$th power. At fixed $X$ the derivative in $Z$ satisfies $t'=-\alpha' t^{1-e}/e$. It lowers a Laurent series valuation by at most $e$ and preserves the valuation lower bound if $\alpha$ is constant. All derivatives of coefficient functions are taken in the separable constant field. Geometrically separate components are handled branch by branch. The curve is reduced by separability.

Write $N=F_{ZZ}F_Y^2-2F_{ZY}F_YF_Z+F_{YY}F_Z^2$. The case $F\mid N$ admits at most three selected points by the [geometric-line argument](second-prime-quartic-intrinsic.md). Hence the proper intersections below are finite. On an affine branch write $j=\operatorname{ord}F_Y$. Implicit differentiation gives $N=-F_Y^3 Y''$. At a finite point of ordinate $\beta$ let $s=\min(e,\operatorname{ord}(Y-\beta))$ be the branch multiplicity, and $\nu=\min(\operatorname{ord}F_X,j)$. A smooth point has $\nu=0$. At any singular point of total multiplicity $r$, $\nu\ge s(r-1)$ because a partial derivative has local order at least $r-1$. If $s=2$, then $\nu\ge3$: the only case left by this last bound is $s=r=2$, when this is the sole branch and its quadratic tangent cone is its doubled tangent line. The leading partials are multiples of that tangent, which has order at least three on the branch. If $s=3$ then $\nu\ge6$.

At every finite singular branch,
\[
 \operatorname{ord}N\ \ge\ 8\nu/3. \tag{2}
\]
For $e=1$ the branch is a regular series in $X-\alpha$, and its second $Z$ derivative at fixed $X$ is regular. For $e=s\ge2$, subtract the constant term and the $t^e$ term from $Y$. Both have regular second derivatives because $t^e=X-\alpha$. The remainder has order at least $e+1$, hence $\operatorname{ord}Y''\ge1-e$. Now $j\ge\nu$ and $\nu\ge3(e-1)$. For $e>s$, $\operatorname{ord}(Y-\beta)=s<e$, and differentiation in $X$ of the series gives $\operatorname{ord}(dY/dX)=s-e$, since $s<p$. Thus $j=\nu+e-s$, and $\operatorname{ord}Y''\ge s-2e$. These give $\operatorname{ord}N\ge3\nu+e-2s$. The only negative value of $e-2s$ is $-1$ at $(e,s)=(3,2)$, where $\nu\ge3$.

At the received ordinate $\beta=L_x(Z)$ over a fixed domain site $\alpha=x\in k$, differentiation preserves the order of $Y-L_x$ and $L_x''=0$. Thus $\operatorname{ord}N\ge3\nu+s$ there, also on smooth branches. Summing $s$ over the branches at the point gives its multiplicity $\ell_x$. The extra contribution beyond $8\nu/3$ is at least
\[
 \ell_x+\ell_x(\ell_x-1)/3\ \ge\ (5\ell_x-2)/3
\]
when $\ell_x>0$, using the earlier lower bound $\nu\ge s(\ell_x-1)$. The right side is negative at $\ell_x=0$, so it still gives an admissible lower bound for that site's extra contribution.

At $Y=\infty$ use $T=1/Y$, $S=T^3F(1/T)$ and write $f=\operatorname{ord}T>0$, $j=\operatorname{ord}S_T$. The generic homogeneous polar on this chart reduces to $S_X-\lambda T^2 S_T$ modulo $S$. From $dT/dX$ one gets $\operatorname{ord}S_X=j+f-e$; here $f<p$ since the sum of all these $f$ at finite $X$ is the degree of the value-leading coefficient $a$, at most $W-3d$. Consequently $\nu=j+f-e$. The homogeneous Hessian on the branch is $T^4 S_T^3(1/T)''$, as in the [infinity computation](second-prime-normalized-hessian.md). Its order is at least $3f+3j-2e$. After reserving $f$ for the universal divisor $a$, the remaining order is at least $8\nu/3-2f/3$, since $3j+2f-2e-(8\nu/3-2f/3)=(j+2e)/3\ge0$.

The normalized Hessian has degree at most $H=15W-24d$. Summing (2), the received-point surplus, and the infinity charge yields
\[
 5\sum_x\ell_x\ \le\ 2n+3H-8g+2(W-3d). \tag{3}
\]

## The finite production instance

Fix $t=379125682$ agreements. The first interpolant has total degree at most 33 and value degree at most three, with dimension surplus $28432674$. At most three affine heads, three nonlinear components of value degree at most two, and 33 vertical labels together account for fewer than $2n$ points using the [low-degree bounds](second-prime-quadratic-discriminant.md). In detail the estimates are $e+1$ per head and $4128$ per nonlinear component of total degree at most 34, with $e=n-t$. There is thus an irreducible cubic-in-$Y$ factor carrying at least $M=2n+1-33=2147483616$ selected points. An interpolant of total degree at most ten and value degree at most five exists with surplus $142274788$. Bézout forces it to contain this factor, so $m\le10$.

With $h=214748361$, the full space of degree-$(h,5)$ interpolants has dimension at least $41742639225021161$. Each is divisible by $F$ since $10h<M$. At weight $W\ge248381593$ the quotients, of total degree at most $h-3$ and value degree at most two, would have capacity only $41742638856158859$. Therefore $W\le248381592$. In (1) the integer defect is at most 33 uniformly: $2D-2J=10W-16d-6$ is increasing in $W$, $H_p\le51$, and $M_1\ge2147483572$. Thus $g\ge2(W-d)-33$. Substitution into (3) leaves a right side increasing in $W$, giving $\sum_x\ell_x\le1137312751$.

Finally apply the [polynomial-multiplier jet argument](second-prime-intrinsic-cubic.md) with $\mu=4287$ and scalar total degree $s=715827867$. The jet codimension sum is at most $(\mu-1)\sum_x\ell_x+n$. The number of coefficients exceeds the total net number of restrictions by $48948548771097$. The resulting nonzero polynomial of value degree at most two must vanish on all $M$ selected points. Its resultant with $F$ in the value variable has scalar degree at most $3s+2(10-3)=2147483615<M$. This proves the claimed contradiction, and Hamming-step constancy gives the stated lower endpoint. This is a written proof with a checked exact-arithmetic certificate. [Finite checker](../../../scripts/probes/probe_second_prime_persistent_singularities.py)
