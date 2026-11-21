# A polynomial proof of the $h+2$ rate-half MCA bound

This proves the unrestricted $h+2$ numerator in the [rate-half predecessor theorem](rate-half-apolar-predecessor.md) using polynomial identities over a field. It provides an alternative to finite-flat duality and sheaf cohomology for this bound.

Keep the syndrome notation of the theorem. Work over an algebraic closure $k$ of the alphabet, with one parameter $T$, and let $K_t=k(T)$. Suppose at least $M>e+1$ parameters are bad, where $n=4h$, $k_{\mathrm{RS}}=2h$, $e=h-1$, and $d=2h-1$. The $(e+1)$-row minors of the syndrome catalecticant vanish identically because they have degree at most $e+1$ in $T$. Take a minimal nonzero apolar form of degree $r\le e$ over $K_t$. The identically zero syndrome pencil can be discarded. Clear denominators to obtain
$$
f(T,Y)=a_0(T)+\cdots+a_r(T)Y^r
$$
with coefficients in $k[T]$ of greatest common divisor one and maximum degree $l$. A fixed projective change of coordinate places the finite evaluation set away from zero and infinity and ensures $a_0a_r\ne0$ over $K_t$. Such a choice exists over the infinite field $k$. The transformed received syndrome remains a pencil linear in $T$, and evaluation functionals form a scaled moment curve in the new coordinates. The argument is invariant under these nonzero scales. At every parameter $\tau$, the polynomial $f_\tau$ is nonzero, including when its affine degree drops. Its homogenization still has degree $r$ on the coordinate projective line. Write $K(Y)=\prod_{x\in H}(Y-x)$ for the transformed squarefree domain vanisher, up to a nonzero constant.

## The parameter degree of the locator

Over $K_t$, let $A=K_t[Y]/(f)$. Reduction modulo $f$ gives a functional $L$ on $A$ such that $L(\overline g)=\lambda_T(g)$ for all $\deg g\le d$. Indeed the remainder has degree less than $r$ and $\lambda_T$ annihilates the subtracted multiple of $f$. The pairing $(b,c)\mapsto L(bc)$ is nondegenerate. Its radical is an ideal of $A$; a nonzero ideal gives a proper quotient of dimension $r'<r$ on which $L$ factors. The monic defining polynomial of this quotient is then apolar of degree $r'$, contrary to minimality.

Let $s=d-2r+2$. For homogeneous coordinate variables $U,V$, consider the determinant
$$
\Delta(T;U,V)=
\det\big(\lambda_T(Y^{i+j}(VY-U)^s)\big)_{0\le i,j<r}.
$$
The entries use moments of degree at most $2r-2+s=d$ and have parameter degree at most one. In $K_t[U,V]$, this matrix is the Gram matrix of $L$ times the matrix of multiplication by $(VY-U)^s$ on $A$. The determinant of multiplication by $U-VY$ in the monomial basis is the homogenization of $f(T,U)/a_r(T)$, since the matrix of multiplication by $Y$ is its companion matrix. Consequently
$$
\Delta(T;U,V)=c(T)\big(V^r f(T,U/V)\big)^s
$$
with $0\ne c(T)\in K_t$. Because the coefficients of the homogeneous $f$ are primitive over $k[T]$, Gauss's lemma shows that $c(T)$ is a polynomial. The degree in $T$ gives $s l\le r$. In particular $l\le\lfloor e/3\rfloor$.

## Two affine charts

Define the divided difference and its syndrome polynomial by
$$
P(T,X)=\lambda_T^Y\!\left(\frac{f(T,X)-f(T,Y)}{X-Y}\right).
$$
The superscript indicates that the functional acts only on the variable $Y$. The quotient is a polynomial. One has $\deg_T P\le l+1$. Moreover $P$ and $f$ are coprime in $K_t[X]$. Indeed for a common geometric root $x$ of $f$ and $P$, the form $q(Y)=f(T,Y)/(Y-x)$ of degree $r-1$ satisfies $\lambda_T(q)=P(T,x)=0$. Every polynomial $g(Y)$ of degree $\le d-r+1$ can be written as $g(x)+(Y-x)v(Y)$ with $\deg v\le d-r$. Hence $\lambda_T(qg)=0$. This contradicts minimality, which is unchanged by scalar extension since existence of an apolar polynomial in a given degree is a matrix rank condition.

In the reciprocal coordinate, use
$$
f'(T,Y)=Y^r f(T,1/Y),\quad
\lambda'_T(g(Y))=\lambda_T(Y^d g(1/Y)),\quad
K'(Y)=Y^n K(1/Y).
$$
The prime indicates reversal here. It denotes no derivative. Define $P'$ by the same divided-difference formula using $f'$ and $\lambda'$. As a Laurent polynomial identity modulo $f(T,X)$,
$$
P'(T,1/X)\equiv -X^{d+2-r}P(T,X).
\tag{1}
$$
For the direct computation, combine both divided differences with a common denominator $X-Y$. In the quotient by $f(T,X)$ the numerator becomes
$$
X \big(Y^{d+1-r}-X^{d+1-r}\big)f(T,Y).
$$
Dividing this numerator by $X-Y$ produces $f(T,Y)$ times a polynomial of degree at most $d-r$ in $Y$. It is killed by $\lambda_T$. This cancellation can be made before specialization: the residual multiple of $f(T,X)$ is also a Laurent polynomial since each difference of two equal powers is divisible by $X-Y$.

At any bad $\tau$, write $\lambda_\tau=\sum_a w_a\mathrm{ev}_a$ with at most $e$ distinct error sites and $w_a\ne0$. Apolarity gives $\sum_a w_a f_\tau(a) v(a)=0$ for all $\deg v\le d-r$. Interpolating the delta functions on the support yields $f_\tau(a)=0$ for every $a$, since $d-r\ge e-1$. Thus
$$
P(\tau,X)=\sum_a w_a\, f_\tau(X)/(X-a),
\qquad f_\tau(X)\mid K(X)P(\tau,X).
\tag{2}
$$
The formula also holds for an empty support at a zero syndrome specialization. Applying the same argument with reversed coordinates gives $f'_\tau\mid K'P'(\tau,\cdot)$; the error weights there are rescaled by $a^d$ and all $a$ are nonzero. Equation (2) holds with multiplicities even when $f_\tau$ has repeated roots.

## Interpolating the quotients

Suppose $M\ge3l+3$ and let $S(T)=\prod_\tau(T-\tau)$ over the chosen bad parameters. Set $m=3$, $b=n-3(d+2-r)<r$ and $U(T,X)=P(T,X)^3 K(X)$. If $l=0$, the locator is constant. All its fixed error sites lie in the coordinate domain as soon as there are two nonzero close members with the generic support. More directly, the generic nonzero-divisor property of $P$ and the degree-$3$ identity $f\mid U(\tau,\cdot)$ at every bad parameter imply $f\mid U$ by coefficient interpolation as soon as $M>3$, hence $f\mid K$. We may therefore assume $l\ge1$.

For each $\tau$ the polynomial $U(\tau,X)/f_\tau(X)$ exists by (2). Interpolate these polynomials coefficientwise in $T$ to obtain $Q(T,X)$ of parameter degree less than $M$. Then
$$
B(T,X)=\frac{U(T,X)-f(T,X)Q(T,X)}{S(T)}
$$
is a polynomial in both variables. Its parameter degree is at most $l-1$, since $\deg_T U\le3l+3<M+l$ and $\deg_T(fQ)<M+l$. Carrying out the construction in the second coordinate chart produces $B'(T,Y)$ of the same parameter degree. Use the negative of the reciprocal divided difference as the chart witness, absorbing the minus sign in (1). Then (1) and $K'(1/X)=X^{-n}K(X)$ give
$$
f(T,X)\mid S(T)\big(B'(T,1/X)-X^{-b}B(T,X)\big)
$$
in $k(X)[T]$. No $T-\tau$ divides $f(T,X)$ in this ring, because $f_\tau(X)$ is nonzero. Cancel $S$. The divisor $f$ has parameter degree exactly $l$ in $k(X)[T]$, whereas the difference has smaller degree. The difference is therefore zero. It follows from the Laurent powers of $X$ that $B=0$ if $b<0$, and otherwise that both chart polynomials have coordinate degree at most $b<r$.

Choose the homogeneous parameter coordinates at the outset so that zero and infinity are outside the selected set. This is possible over the infinite algebraic closure. On the reciprocal parameter chart $t=1/T$, use $\widetilde f(t,X)=t^l f(1/t,X)$, $\widetilde\lambda_t=t\lambda_{1/t}$, and $\widetilde S(t)=t^M S(1/t)$. Interpolation as above applies to $\widetilde S$, which differs by a nonzero constant from the monic reciprocal-node vanisher. It supplies a polynomial $\widetilde B(t,X)$ of coordinate degree at most $b$ as well. The reciprocal parameter version of $U$ is exactly $t^{3(l+1)}U(1/t,X)$. Both quotient identities, now viewed in $k(T)[X]$, give
$$
f(T,X)\mid \widetilde B(1/T,X)-T^{M-3(l+1)}B(T,X).
$$
Both terms have coordinate degree less than $r=\deg_X f$. Hence this divisibility is an equality with zero remainder. If $M>3l+3$, the first Laurent polynomial has only nonpositive powers of $T$, whereas the second has only positive powers. Thus $B=0$. Returning to the original interpolation identity gives $f\mid P^3 K$ and then $f\mid K$ by coprimality. The fixed-support argument in the main proof gives at most $r$ bad scalars.

We have proved $M\le3l+3\le3\lfloor e/3\rfloor+3=h+2$. When $M=3l+3$ the Laurent identity instead implies that $B$ is independent of $T$ and is an ordinary coordinate polynomial of degree at most $b$. These chart calculations also hold when some specialized locators have repeated roots or lose rank. The exact homogeneous coordinate divisor at the extremum is identified in the main proof.
