# A moving cubic bound at the second prime

Let $n=2^{30}$, $d=2^{26}-1$, and $p=730750818665451459101842416358141509841924915201$. On any $n$ distinct points of this prime field, the degree-at-most-$d$ Reed–Solomon code has at most $2n$ MCA-bad scalars at $e=655110340$ errors. A dimension comparison below extends this bound through **664797186 errors**, so the first bad error count is at least **664797187**. The three-core example gives the upper bound **715827882**. This is a written proof with separately kernel-checked ingredients.

## Two interpolation polynomials

Write $k=\overline{\mathbb F}_p$, $K=k(X)$, and $t=n-e=418631484$. For each bad scalar $z$, choose a witness $q_z(X)$ of degree at most $d$ with at least $t$ agreements with the received fold $u+zv$. For integers $s,b$, take monomials $X^aZ^iY^j$ with $j\le b$, $i+j\le s$, and $a+dj<t$. Vanishing identically on the line $Y=u(x)+Zv(x)$ costs at most $s+1$ linear conditions at each domain site $x$. A surplus of coefficients gives a nonzero interpolant. Each specialization $Q(X,z,q_z(X))$ has degree less than $t$ and at least $t$ roots, so it vanishes identically.

For $(s,b)=(5,5)$ the surplus is $21t-35d-6n=15$. For $(s,b)=(7,3)$ it is $26t-34d-8n=12782650$. Factor the corresponding $Q_5,Q_7$ in $K[Z,Y]$. Removing their gcd and applying plane Bézout leaves at most 35 witness points outside the common components. Factors depending only on $Z$ contribute at most five distinct scalars in the quintic. Take a primitive integral representative in $k[X,Z,Y]$ for each irreducible common factor. Its $X$-degree is at most $t-1$ because it divides the original quintic after removing the latter's coefficient content in $k[X]$.

## Differentiation in the evaluation coordinate

Fix a common irreducible factor $F$ of total $(Z,Y)$-degree $m\le5$ and $Y$-degree $1\le b\le3$. In $L=k(X,Z)[Y]/(F)$ let $y$ be the residue of $Y$, and put $J=F_Y$. The extension is separable because $b<p$. The derivation $\partial$ with $\partial X=1$, $\partial Z=0$ and $\partial k=0$ extends uniquely. Put $N_1=-F_X$ and
\[
 N_{r+1}=J^2(N_r)_X-J F_X(N_r)_Y
    -(2r-1)N_r(J J_X-F_XJ_Y).
\]
Differentiation gives $N_r=J^{2r-1}\partial^r y$ in $L$. The identity holds also after substituting $Z=z,Y=q_z(X)$ on $F$. To see this even when $J$ specializes to zero, differentiate the previous identity, multiply by $J^2$, and use $Jq'_z=-F_X$. Every such witness therefore annihilates $N_{d+1}$.

The recurrence bounds the total degree of $N_r$ by $m_r=m+2(r-1)(m-1)$, its $Y$-degree by $b_r=b+2(r-1)(b-1)$, and its $X$-degree by $(2r-1)t$. If $F$ does not divide $N_{d+1}$, their resultant in $Y$ is a nonzero member of $K[Z]$. For respective total degrees at most $m,m'$ and actual $Y$-degrees $b,b'$, the resultant has $Z$-degree at most $b'm+bm'-bb'$. A Sylvester determinant term selects $b'$ coefficients of the first polynomial and $b$ of the second. Their coefficient indices sum to $bb'$ by subtracting the row shifts from the sum of the column indices. A coefficient at index $i$ has parameter degree at most $m-i$ or $m'-i$. Replacing $b'$ by its upper bound is valid since $m-b\ge0$. Every distinct scalar on $F$ is a root of the resultant. The resulting upper bound is
\[
 H(m,b)=2mb-b^2+2d(2mb-m-b^2).
\]
In particular $H(5,3)=21+32d=2147483637$, eleven below the budget.

## The identically vanishing derivative

If $F\mid N_{d+1}$, then $\partial^{d+1}y=0$ in $L$. Since $d+1<p$, define
\[
 c_j=\frac{1}{j!}\sum_{i=0}^{d-j}\frac{(-X)^i}{i!}\partial^{i+j}y \qquad(0\le j\le d).
\]
Successive terms cancel on differentiation, giving $\partial c_j=0$. The binomial theorem gives $y=\sum_{j=0}^d c_jX^j$. Positive characteristic requires a height bound before these constants can be treated as algebraic over $k(Z)$.

Give each expression for $c_j$ the common denominator $J^{2d}$. Its numerator and denominator have $Y$-degree at most $10(d+1)$ and $X$-degree at most $4(d+1)(t+1)$. Indeed each $N_r$ contributes $Y$-degree at most $3+4(r-1)$ and is multiplied by $J^{2d-(2r-1)}$. The $r=0$ summand uses $yJ^{2d}$. The $X$-degree estimate includes the powers of $-X$. Write the resulting quotient as $A/B$. The polynomial $\operatorname{Res}_Y(F,A-WB)\in k(Z)[X,W]$ is nonzero since $B$ is a power of $J$ and does not vanish in $L$. It vanishes at $W=c_j$ and has $X$-degree at most $22(d+1)(t+1)<p$ by the ordinary Sylvester degree bound.

The primitive minimal polynomial of $c_j$ over $k(Z)(X)$ divides this resultant in $k(Z)[X,W]$ and inherits its $X$-degree bound. Divide by its leading coefficient in $W$ and differentiate its equation at $c_j$. The differentiated coefficient polynomial has smaller $W$-degree and still annihilates $c_j$, so every differentiated coefficient vanishes. A rational function in $X$ over $k(Z)$ with derivative zero lies in $k(Z)(X^p)$. A reduced numerator and denominator of degree less than $p$ force it to belong to $k(Z)$. Thus each $c_j$ is algebraic over $k(Z)$.

Every conjugate of $y$ is consequently a polynomial in $X$ of degree at most $d$ with coefficients algebraic over $k(Z)$. Their monic product has coefficients in $k(Z)[X]$, by intersecting the polynomial ring over the algebraic constants with $k(Z)(X)$. Its primitive integral form $F$ has $Y$-leading coefficient depending only on $Z$. For each domain site put $R_x(Z)=F(x,Z,u(x)+Zv(x))$. If $R_x=0$, one conjugate takes the base-field value $u(x)+Zv(x)$ there. Hence all conjugates do, by extending the conjugate maps on coefficients over the independent indeterminate $X$. If there are more than $d$ such sites, interpolate $u,v$ at $d+1$ of them, giving degree-at-most-$d$ polynomials $A_0,B_0$ over the original prime field. Uniqueness now gives $y=A_0+ZB_0$, a genuine affine head. Each scalar on this head needs a fresh agreement outside its joint core. Distinct scalars have disjoint fresh agreements, giving at most $e+1$ bad scalars as in the rate-sixteenth proof.

If there are at most $d$ identity sites, all other $R_x$ are nonzero of degree at most $m$. Counting their roots gives $M(t-d)\le m(n-d)$ for $M\ge m$ witnesses on the factor. This bounds $M$ by 14 at the stated parameters. The same numerical bound covers $M<m$. A specialization of the leading coefficient causes no exception to this incidence count.

## Summing all scalar labels

If a cubic-in-$Y$ component occurs, the remaining factor in $Q_7$ depends only on $Z$ and has degree at most $7-m$. It bounds every scalar outside that component, including scalars outside the common divisor. If $m=5$, $Q_5$ is already a unit multiple of this component and there are no additional scalars. For $m\le4$, $H(m,3)\le H(4,3)=15+22d$ leaves room for the at most four additional labels. The affine-head and 14-point alternatives also fit.

If every common component has $Y$-degree at most two, the sum of their positive $Y$-degrees is at most three. A degree-one component carries at most $\max(H(5,1),e+1,14)=e+1$. A degree-two component carries at most $\max(H(5,2),e+1,14)=16+22d$. Thus the total, including the at most 35 isolated points and the at most five vertical labels, is bounded by
\[
 40+\max\{3(e+1),\,16+22d+(e+1)\}<2n.
\]
This proves the bound for the full witness-set MCA event. Monotonicity and the integer Hamming grid give the first-bad lower endpoint. The argument bounds the numerator on arbitrary injective domains over primes $p>22(d+1)(t+1)$. The second prime's budget translates it into the security statement above.

[Rate-sixteenth core and packing proofs](rate-sixteenth-mca-threshold-curve.md) · [Lean interpolation](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuarticInterpolation.lean) · [Finite incidence and norm-section lemmas](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeComponentIncidence.lean)

## The stronger dimension bound at 664797186 errors

At the second production prime and rate $1/16$, the moving-cubic argument and a dimension comparison give the written bound
$$
664797187/1073741824\ \le\ \delta^*\ \le\ 715827882/1073741824.
$$
Set $n=1073741824$, $d=67108863$, $t=408944638$ and $e=n-t$. Suppose $2n+1$ distinct bad scalars have been selected. All polynomials below use coordinate weight one for $X$, weight $d$ for $Y$ and zero for the scalar variable $\Gamma$. Weight below $t$ makes every interpolant vanish identically on each selected polynomial witness when the scalar is specialized.

An interpolant of total $(\Gamma,Y)$-degree at most 9 and $Y$-degree at most 3 exists. Its four rows of coefficients have $10,9,8,7$ choices of scalar exponent, so the dimension surplus is $34t-46d-10n=79691754$. If every positive-$Y$ factor had degree at most two in $Y$, the preceding small-factor bounds would exclude the given witness count: there are at most three affine heads, with $3(e+1)$ labels in total, at most three nonlinear factors with at most 4128 labels each, and at most nine parameter-only labels. These generous bounds sum to less than $2n$. Therefore there is one irreducible cubic-in-$Y$ factor $F$ over $\overline{\mathbb F}_p(X)$, and all other factors of this interpolant are independent of $Y$. At least $2n+1-9$ selected points lie on $F$.

Now take the entire vector space of interpolation polynomials of total $(\Gamma,Y)$-degree at most seven and coordinate weight below $t$. The possible $Y$-degrees are $0,\ldots,6$. There are $35t-77d$ coefficients and at most $8n$ linear conditions, so its dimension is at least **555745287**. Every one of its members vanishes on the same selected points. By plane Bézout over $\overline{\mathbb F}_p(X)$, each nonzero member is divisible by $F$, since at most $7\cdot9$ intersection points would otherwise lie on $F$. Take an integral representative primitive over $\overline{\mathbb F}_p[X]$; Gauss's lemma makes the quotients integral polynomials.

If $F$ had total $(\Gamma,Y)$-degree at least six, every quotient would have total degree at most one in those variables and weight below $t-3d$, since $F$ has weight at least $3d$. The $1,\Gamma,Y$ coefficient slots then give dimension at most **$2(t-3d)+(t-4d)=555745284$**, three below the proved lower bound. Thus $F$ has total degree at most five. The [moving-cubic derivative and inverse-Taylor argument](second-prime-moving-cubic.md) now applies. Its nonzero-derivative cap is at most $21+32d=2147483637$, below the $2147483640$ selected points on $F$. In the identically-zero case either the factor is a single affine head or there are at most $5(n-d)/(t-d)<15$ points there. These contradictions prove goodness at $e=664797186$ errors. Hamming-step constancy gives the lower endpoint above. The decisive dimension comparison is $32t>8n+67d$, whose first integer solution is the stated $t$. This does not require a degree-six cubic derivative bound. The dimension and endpoint comparison here are written mathematics, not a new kernel-verification claim.
