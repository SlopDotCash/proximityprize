# Bounding tangent denominators by two plane resultants

For a nonlinear factor of a received-line interpolant, one can bound the sum of the heights of its rational tangent heads using the reduced binary discriminant. The proof below uses the tame lifting of derivations at a discrete valuation ring. It gives an algebraic route to the nonlinear step in the [three-head threshold through dimension 71,582,789](three-heads-above-one-sixteenth.md). At the sextic parameters it bounds the populations in degrees two through six by **8,489, 23,267, 44,589, 70,367 and 98,657**. Lean proves the tame local lifting step for a derivation of the fraction field. Lean also constructs specialization on every retained simple section over the original coefficient ring and proves the resulting denominator divisibility. Lean assembles branchwise regularity over all prime divisors of the plane. Applying the local regularity criterion to the two displayed derivations still requires identifying their ramified divisors and checking the local hypotheses. Lean proves the local iterated-derivative identity, reciprocal clearance, the total two-resultant height budget given its fiber divisibilities, and the five prices. Independent kernel checks accepted 19,217 declarations for these steps and 16,367 for the incidence count. [Resultant and derivative theorems](../../../ArkLib/Research/ProximityGap/Frontier/LogarithmicSectionHeights.lean) · [Counting inequality](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadCount.lean)

A separate surface Gauss graph calculation bounds the sum of the retained denominator degrees by $(6b+2)Wm$ when the characteristic is zero or exceeds $2Wb$. [Proof and second-prime half-rate application](gauss-polar-section-heights.md)

## Hypotheses and bound

Over an algebraically closed field $k$, take a primitive irreducible polynomial $F(X,Z,Y)$ of value degree $b\ge2$, total $(Z,Y)$ degree at most $m$, and coordinate weight at most $W$ when $Y$ has weight $d$. Consider $M$ distinct $z$ with $F(X,z,q_z(X))=0$, $\deg q_z\le d$. At least $t$ of $n$ distinct sites satisfy $q_z(x)=u_0(x)+zu_1(x)$ for each $z$. Write
$$A=(2b-2)W-b(b-1)d,\quad G=(2b-2)m-b(b-1),\quad C_0=2AG+2Wm.$$
Assume $t^2>nd$ and characteristic zero or larger than $\max(A,b)$. Then
$$M\le G+(2b-1)m+m+
\left\lfloor\frac{2t(G+m)n+n(2C_0+mn)}{t^2-nd}\right\rfloor.$$
The bounds $A,G$ are the respective degrees in $X,Z$ of the binary discriminant. The ordinary discriminant is enough after recording these bounds. [Binary discriminant bounds](hodge-section-variance.md#a-population-inequality-without-a-weight-restriction)

First discard the at most $(2b-1)m$ labels at which the value resultant of $F,F_Y$ vanishes identically in $X$, and the at most $m$ labels where the leading value coefficient vanishes identically. Each remaining tangent velocity $V_z=-F_Z(X,z,q_z)/F_Y(X,z,q_z)$ belongs to $k(X)$. Choose $r$ away from the sites and all poles of these finitely many functions. Set $T=1/(X-r)$ and replace $Y$ by $T^dY$. Each transformed section is polynomial, and the transformed velocity $T^d V_z(r+1/T)$ has pole order at infinity at most $d$. The transformed equation, cleared by $T^W$ and made primitive, obeys the same two degree bounds and stays separable at each retained section. The received lines transform by the same factor. Hence, using the new coordinate as $X$, a bound on the *finite* denominator degree $c_z$ gives a numerator of degree at most $d+c_z$.

## Two derivations preserving the branch divisor

On this affine chart omit from the scalar base the horizontal components $Z=z$ of the discriminant, losing at most $G$ labels. Factor the reduced discriminant remaining there into the vertical part $U(X)$ and the product $H(X,Z)$ of the other irreducible factors, using $1$ for an empty product. In the quadratic or higher function-field extension cut out by $F$, consider the lifts of
$$D_1=H\partial_Z,\qquad D_2=U(H_X\partial_Z-H_Z\partial_X).$$
Both derivations preserve each ramified height-one prime on the base.
Off the binary discriminant the root algebra of the binary form is étale.
At a ramified divisor let $R$ be the base DVR and $B$ the localization of
its finite normalization at the chosen prime. The ramification index $e$
is invertible in $B$, and the residue extension is separable, because
the field degree is at most $b$ and the characteristic exceeds $b$.
Write the base uniformizer as $\pi=u^e v$ with $u$ a uniformizer of $B$
and $v$ a unit. Each field derivation $D$ preserves $R$ and satisfies
$D\pi\in\pi R$.

A common denominator for the derivatives of finite module generators
clears every derivative on the finite normalization by the product rule.
The denominator becomes a unit times $u^m$ in $B$. The quotient rule
extends the same bound to every element of its localization.
Write $\delta=u^mD$, so $\delta(B)\subseteq B$. Differentiating $u^ev$,
canceling $u^{e-1}$ and using $\delta\pi\in u^e B$ gives
$e v\,\delta u\in uB$, hence $\delta u\in uB$. If $m>0$, $\delta$
also vanishes on $R$ modulo $u$. For any $b\in B$, lift the residue
minimal polynomial of $\bar b$ to $f\in R[T]$. Then $f(b)\in uB$
and $f'(b)$ is nonzero modulo $u$. Differentiating gives
$f'(b)\delta b=0$ modulo $u$, so $u^{m-1}$ already clears every
$D b$. Descent to $m=0$ proves $D(B)\subseteq B$ and $D u\in uB$.
Lean proves this theorem for the actual fraction-field derivation with
the finite algebra, localization and residue extension as inputs. Independent
verified kernel replay accepted all 10,568 declarations of its dependency closure.
[Local lifting theorem](../../../ArkLib/Research/ProximityGap/Frontier/TameLogarithmicDVR.lean)

At an unramified branch the same argument applies even when $D$ moves the base divisor. The base uniformizer is $\pi=uv$ for a unit $v$. Apply the logarithmic theorem to $\pi D$, which is tangent to $u$ and kills the base modulo $u$. Separable residue lifting gives $(\pi D)(B)\subseteq uB$. Canceling $u$ gives $D(B)\subseteq B$. Lean proves this directly with the finite localization and residue extension as inputs. [Unramified lifting theorem](../../../ArkLib/Research/ProximityGap/Frontier/UnramifiedDerivationDVR.lean)

For a Noetherian UFD $A$ with fraction field $K$ and a finite separable extension $E/K$, Lean constructs the following intersection. At each prime element $p$, let $C_p$ be the integral closure of the DVR $A_{(p)}$ in $E$. It is finite over $A_{(p)}$ and Dedekind. Membership in all its localizations at nonzero primes gives membership in $C_p$. If $x$ lies in every $C_p$, every coefficient of its minimal polynomial over $K$ belongs to every $A_{(p)}$. A prime factor of a nonunit reduced denominator would contradict regularity at its own prime, so each coefficient lies in $A$. The minimal polynomial gives integrality over $A$. In the plane application the existence of the retained simple section already gives separability of the generic polynomial. As a consequence, branchwise regularity of either derivation on these explicit DVRs gives denominator divisibility on every retained simple section. Independent verified kernel replay accepted 33,313 declarations for this combined theorem and the DVR and finiteness statements. [Height-one assembly and application](../../../ArkLib/Research/ProximityGap/Frontier/HeightOneNormalization.lean)

The remaining geometric input is regularity of the two specified field derivations at each upstairs branch. This uses the unramified case off the binary discriminant and the tame logarithmic criterion on its ramified divisors. For the general geometric lifting theorem and the local structure see [Källström, liftable derivations](https://arxiv.org/abs/math/0604559) · [Tame extensions of discrete valuation rings](https://stacks.math.columbia.edu/tag/0EXT)

For a constant $a$ put $A_a=F(X,Z,a)$. The reciprocal root $S_a=A_a/(Y-a)$ is integral. The reversed Taylor polynomial of $F$ at $a$ has leading coefficient $F(a)$ when this value is nonzero, so scaling its reciprocal root gives an integral element. When $F(a)=0$ the reciprocal is zero. Thus $D_i S_a$ is integral as soon as $D_i$ preserves the normalization.

For a retained section write $R=k[X]$ and $L=k(X)$. The Taylor map $Z\mapsto z+T$ embeds $L[Z]$ into $L[[T]]$. The leading value coefficient becomes a unit and Hensel lifting gives an actual root $y(T)$ with $y(0)=q_z$. Evaluating the generic root algebra at this root maps it into $\operatorname{Frac}(L[[T]])$. Every element integral over $R[Z]$ maps into $L[[T]]$, since that ring is integrally closed. Taking constant terms of the same monic relation proves that its constant term is integral over $R$, hence lies in $R$. These evaluations form one ring homomorphism on a subring containing the entire normalization and the generic ordinate. It sends every $G(Z,Y)$ to $G(z,q_z)$, including when the generic ordinate itself is nonintegral. Lean proves this construction for any integrally closed domain $R$ and its fraction field.

Writing $F^\delta$ for the polynomial obtained by applying a base derivation $\delta$ to each ordinate coefficient, the formal endpoint is
$$
 F_Y(z,q_z)\ \mid\ A_a(z) F^\delta(z,q_z) \quad\text{in }R.
$$
It assumes an extension of $\delta$ to the generic field that preserves the integral closure, and $Y\ne a$. Differentiating $F(Y)=0$ supplies the generic tangent equation. The identity
$$A_a D_iY=(D_i A_a)(Y-a)-(D_i S_a)(Y-a)^2$$
then makes $A_aD_iY$ polynomial on the section. The $X$ derivative of $Y$ specializes to $q_z'$ by differentiation of the section equation. If $D_z$ is the reduced denominator of $V_z$, it follows that $D_z$ divides both $A_a H$ and $A_a UH_X$, evaluated at $Z=z$. Independent kernel replay accepted 21,521 declarations for the specialization and divisibility theorems. [Formal specialization and denominator theorem](../../../ArkLib/Research/ProximityGap/Frontier/NormalizedSectionSpecialization.lean)

Choose two constants $a,a'$ for which $A_a,A_{a'}$ are coprime in $k[X,Z]$. Such a pair exists: after choosing the first, each of its finitely many irreducible factors can divide $F(X,Z,a')$ for only finitely many $a'$, because $F$ is primitive in $Y$. Also exclude every constant for which $F(X,z,a)$ vanishes identically at any retained label, for both choices. Each of these finitely many nonzero value polynomials has at most $b$ constant roots over $k(X)$. The preceding two divisibilities imply
$$D_z\mid \gcd(A_a(X,z),A_{a'}(X,z))\,\gcd(H(X,z),U(X)H_X(X,z)).$$
Here $H$ and $UH_X$ are coprime because $H$ is squarefree with no vertical or horizontal factors and its $X$ degree is below the characteristic. When $H=1$ the second gcd is one. The sum of the specialized gcd degrees of any coprime pair $P,Q$ is bounded by the scalar degree of $\operatorname{Res}_X(P,Q)$. At each scalar the corank of the specialized Sylvester matrix is at least the gcd degree, including degree drops; column reduction shows that the scalar resultant is divisible by that power of $Z-z$. For a specialization where just one polynomial is zero, use the same rank count with the other polynomial. Coprimeness excludes both being identically zero at the same scalar. Polynomials of $X$ degree zero give the same inequality directly. The first resultant therefore costs at most $2Wm$. For the second, $\deg_X U+\deg_X H\le A$, and both scalar degrees are at most $G$, giving at most $2AG$. This proves $\sum_z c_z\le C_0$. [Padded Sylvester syzygies](../../../ArkLib/Research/ProximityGap/Frontier/PaddedPowerSpecialization.lean)

## Ordinary differentiation at a repeated received root

At $x$ write $L(Z)=u_0(x)+Zu_1(x)$ and $F(x,Z,Y)=(Y-L(Z))^j B(Z,Y)$, with $B(Z,L(Z))\ne0$. The specialized form is nonzero by primitivity. Discard the zeros of $H(x,Z)B(Z,L(Z))$, at most $G+m$ scalar incidences at each site. The absence of vertical factors makes $H(x,Z)$ nonzero. At any remaining agreement $j\ge1$ and $Y$ is regular in the local normalization at the section point: take a constant $a$ different from the received value with $F(x,z,a)\ne0$; then $S_a$ and $A_a$ are units there. Evaluating along the section and then at $x$ defines this point on the normalization. The derivation $D_1$ extends to that local ring. It fixes $X-x$. For $f=Y-L$ one has $f^j\in(X-x)$ there, as $B$ is a unit. Applying $D_1$ exactly $j$ times gives
$$D_1^j(f^j)\equiv j!(D_1f)^j\pmod{f}.$$
The left side vanishes in the residue field. Since $j\le b$ is below the characteristic, $D_1f$ vanishes there as well. Dividing by the unit $H$ shows that $V_z$ is regular and $V_z(x)=u_1(x)$. Also $q_z(x)-zV_z(x)=u_0(x)$. Thus at most $(G+m)n$ agreement incidences are lost in total.

Two different rational tangent heads of heights $c_z,c_{z'}$ agree jointly on at most $d+c_z+c_{z'}$ good sites by clearing denominators. A collection with identical tangent data lies on one affine line over $k(X)$, containing at most $m$ selected points by restricting $F$ to that line. Let $N$ be the retained population and let $s_x$ be the number of retained good agreements. Then $Nt\le\sum s_x+(G+m)n$, and $\sum s_x^2\le N^2d+2NC_0+mNn$. Cauchy–Schwarz and expansion of the square give the claimed population bound, including when the error term exceeds $Nt$. [Pairwise tangent comparison](../../../ArkLib/Research/ProximityGap/Frontier/TangentHeadCount.lean)
