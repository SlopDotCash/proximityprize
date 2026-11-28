# Polynomial sections of a quadratic equation in the folded value

Let $G(X,Z,Y)$ be primitive and irreducible over $k[X,Z,Y]$, where $k$ is algebraically closed, $Z$ is the folding scalar and $Y$ is the putative codeword. Suppose its total degree in $Z,Y$ is $m$ and its $Y$-degree is two. Write $\Delta=\operatorname{Disc}_Y G$. Assume characteristic zero or odd characteristic exceeding $\deg_X\Delta$. Fix $n$ distinct grid sites, received rows $u_0,u_1$, a message degree cap $d$, and an agreement threshold $t>d$. The number of distinct scalars $\gamma$ admitting a polynomial $f_\gamma$ of degree at most $d$ with
\[
 G(X,\gamma,f_\gamma)=0,\qquad
 \#\{x:f_\gamma(x)=u_0(x)+\gamma u_1(x)\}\ge t
\]
is at most $(2+8n/(t-d))m$. The bound applies whether or not the formal $(d+1)$st derivative vanishes on the generic curve. When an odd-multiplicity discriminant component depends on $X$, the bound is already $10m$ before using any agreement information.

Write $G=AY^2+BY+C$. Over $k[X,Z]$ factor
\[
       \Delta=B^2-4AC=L(Z)W(X,Z)^2P(X,Z)
\]
with $L$ squarefree, $P$ the product of the odd-multiplicity irreducible factors of positive $X$-degree, and $W$ polynomial, absorbing a constant into $L$. The discriminant is nonzero by irreducibility. Its degree in $Z$ is at most $2m-2$.

## Moving discriminant components

Suppose $a=\deg_X P>0$ and put $h=\deg_Z P$. Over $k(Z)$ the polynomial $P$ is squarefree and separable by the characteristic hypothesis. Its nonzero resultant with $P_X$ therefore has $Z$-degree at most $(2a-1)h$. Exclude scalars where $L=0$, $W(X,\gamma)$ vanishes identically or the leading $X$-coefficient of $P$ vanishes. These three exclusions cost at most $\deg L+\deg_Z W+h$ scalars in total.

At any remaining scalar with a polynomial solution, $\Delta(X,\gamma)=(2A(X,\gamma)f_\gamma+B(X,\gamma))^2$. Thus $P(X,\gamma)$, of full $X$-degree $a$, is a square in $k[X]$. Its gcd with its $X$-derivative has degree at least $a/2$. The specialized Sylvester matrix consequently has corank at least $a/2$. Over the discrete valuation ring at $Z=\gamma$ its determinant vanishes to at least this order, by diagonal reduction. Comparing with $(2a-1)h$ gives at most $4h$ remaining scalars. Including the exclusions, the count is at most $\deg L+\deg_Z W+5h\le5\deg_Z\Delta\le10m$.

## A discriminant depending only on the scalar modulo squares

If $P=1$, the squarefree $L$ is nonconstant, since otherwise $G$ would split over $k(X,Z)$. Use the smooth curve with function field $k(Z,S)$, $S^2=L(Z)$. At points above $Z=\infty$ both $Z$ and $S$ can have poles, with the pole order of $S$ equal to $\deg L/2$ times that of $Z$. At finite places both are regular.

Remove the at most $m-2$ scalars where $A(X,\gamma)$ vanishes identically. For each remaining witnessed scalar choose a point $P_\gamma=(\gamma,S_\gamma)$ on the constant curve such that, in $k(X)$,
\[
          f_\gamma=\frac{-B(X,\gamma)+W(X,\gamma)S_\gamma}{2A(X,\gamma)}.
\]
The quadratic equation gives this choice also when $W(X,\gamma)=0$ identically, in which case either square root works. Distinct scalars give distinct points. In the generic fraction on the curve cancel every common factor $X-x$ of numerator and denominator for constant $x$. Such a factor divides each of $A,B,W$ separately because $S\notin k(Z)$. Cancellation preserves the displayed specialization identity and the scalar-degree caps. Call the resulting numerator and denominator $N(X),E(X)$.

At any physical site $x$, the function $N(x)-(u_0(x)+Z u_1(x))E(x)$ has pole degree at most $c=2m-2$. Indeed $B$ has scalar degree at most $m-1$, $A$ at most $m-2$, and $2\deg_Z W+\deg L\le2m-2$. The pole orders at each place above infinity are bounded by $(m-1)$ times the pole order of $Z$, and the latter sum is two. At a site where this function is nonzero, at most $c$ selected labels can agree. At a site where it vanishes identically, $E(x)$ is a nonzero function by the cancellation above. At most $c$ selected labels can fail to agree there, since all such points are zeros of $E(x)$.

Write $M$ for the number of retained labels. Their $Mt$ agreements force at least $t-cn/M$ sites of the second kind. Choose two labels whose combined number of failures on those sites is at most $2cn/M$ by averaging. They define a unique affine polynomial head $a(X)+Zb(X)$ through their two words with $\deg a,\deg b\le d$. Let $J$ consist of the sites of the second kind where both chosen labels agree. Then $|J|\ge t-3cn/M$, the head matches both received rows on $J$, and at most $c$ selected labels fail at any one site in $J$. The head can contain at most $m$ labels, because $G(X,Z,a+Zb)$ is nonzero by irreducibility and has $Z$-degree at most $m$. Among the other $M-m$ or more labels one has at most $cn/(M-m)$ failures on $J$. If $M>m+4cn/(t-d)$ this word agrees with its head specialization on more than $d$ sites, contradicting the choice of an outside label. Adding back the at most $m-2$ exclusions gives the stated bound. An irreducible equation linear in $Y$ obeys the same argument with the rational function $-C/B$ on the scalar line, with $c=m$ and at most $m$ excluded denominator specializations, unless it is itself an affine polynomial head.

At the second-prime half-rate Johnson pivot the total plane degree of the projected factors under consideration is at most $4386$. The primitive equations there have $X$-degree at most $(v_0+v)W_{\max}$, so their discriminant $X$-degree is below the named characteristic. After the fixed surfaces, integral families and affine heads have been accounted for, the linear and quadratic projected factors above consume at most another $178,192$ labels. An overrun must put at least **466,186,464 labels** on the fixed derivative-degree-at-most-two surfaces or regular nonintegrable ordinary components of ordinate degree at least three. [Folded interpolation and the preceding allocation](folded-radial-mca.md#polynomial-families-on-a-projected-component) · [Exact finite counts](../../../scripts/probes/probe_folded_radial_mca.py)

## Higher ordinate degrees

For a primitive irreducible $G$ of $Y$-degree $b\ge3$ use $\Delta=\operatorname{Disc}_Y G=L W^2P$ with the same factor convention. Assume $0<h=\deg_X P<p$ in positive characteristic and separability in $Y$. Put $a=\deg_X G$, $l=\deg_Z P$. Apart from the three exclusions in the moving-component argument, omit the at most $\deg_Z\operatorname{lc}_Y G$ scalars where the leading $Y$-coefficient vanishes as an $X$-polynomial. Choose one nonzero polynomial solution $f_\gamma$ at each remaining eligible scalar and write $j_\gamma=\deg f_\gamma$. For a zero solution take $j_\gamma=0$. Then
\[
 \sum_{\gamma}
 \max\left\{0,\,
 \frac{h-(2b-4)(a-j_\gamma)}2,\,
 \deg_X G_Y(X,\gamma,f_\gamma)-\deg_X W
 \right\}
 \ \le\ (2h-1)l .
\]

Indeed write $G(X,\gamma,Y)=(Y-f_\gamma)H_\gamma$ over $k[X,Y]$. Addition of $X$-degrees under multiplication gives $\deg_X H_\gamma\le a-j_\gamma$, including a constant or zero solution. The discriminant product identity is
\[
      \Delta(X,\gamma)=\operatorname{Disc}_Y(H_\gamma)
                              G_Y(X,\gamma,f_\gamma)^2 .
\]
Its left side is nonzero. The degree in $X$ of the residual discriminant is at most $(2b-4)(a-j_\gamma)$ by its homogeneous coefficient degree. Thus in $P(X,\gamma)$ the sum of the degrees of the factors with odd multiplicity is at most this number. Its gcd with its derivative has degree at least $(h-(2b-4)(a-j_\gamma))/2$: at a root of multiplicity $e$, the gcd contributes $e-1\ge\lfloor e/2\rfloor$. There is a second lower bound. The squared $G_Y$ divides $W(X,\gamma)^2P(X,\gamma)$ up to a nonzero scalar. At each place where the multiplicity of $G_Y$ exceeds that of $W(X,\gamma)$, the excess is at most half the multiplicity of $P(X,\gamma)$ and is covered by the gcd. The degree of the gcd is therefore also at least $\deg_X G_Y(X,\gamma,f_\gamma)-\deg_X W$. Sum the larger of these two charges and zero against the same Sylvester determinant as before.

The possible positive section degrees in this test can be found from $G=\sum_i G_i(X,Z)Y^i$. Outside the zeros of the leading $X$-coefficients of its nonzero $G_i$, a nonzero section of degree $j$ requires that $\max_i(\deg_X G_i+ij)$ be attained at least twice. Thus only the finitely many integer slopes of this upper envelope need be considered. The displayed bounds can give zero charge for higher-degree factors with a large square part in the discriminant.

There is a second application with $X$ and $Z$ exchanged. For $M>0$ selected scalars, at least $c=t-\lfloor mn/M\rfloor$ physical sites have the entire line $Y=u_0(x)+Zu_1(x)$ on $G(x,Z,Y)$. At every other site the nonzero substitution has $Z$-degree at most $m$ and hence contains at most $m$ agreeing labels. Write $\Delta=L_X(X)W_Z^2P_Z$ by removing squares and the odd-multiplicity factors depending only on $X$. Assume $h_Z=\deg_ZP_Z>0$ is below the characteristic, and put $l_X=\deg_X P_Z$. Count once each grid site where $L_X$ or $\operatorname{lc}_ZP_Z$ vanishes, or where $W_Z$ or $\operatorname{lc}_YG$ vanishes identically in $Z$. Denote their number by $E_X$.

At a remaining site with the entire line, the residual after dividing out its linear factor has total $(Z,Y)$ degree at most $m-1$ and $Y$-degree $b-1$. Its discriminant has $Z$-degree at most $(2b-4)(m-1)-(b-1)(b-2)=(b-2)(2m-b-1)$. Indeed the coefficient of $Y^i$ has $Z$-degree at most $m-1-i$, and every discriminant term has coefficient index weight $(b-1)(b-2)$. The same corank argument in $Z$ yields
\[
 (c-E_X)_+\,[h_Z-(b-2)(2m-b-1)]_+
           \ \le\ 2(2h_Z-1)l_X .
\]
Both directional inequalities apply to the same factor. They leave open the case in which both lower bounds on corank vanish.

## Rational generic sections in any ordinate degree

Suppose a primitive irreducible $G$ of total scalar/value degree $m$ has a root rational in $X$ over $\overline{k(Z)}$. Assume its positive ordinate degree $b$ is smaller than the characteristic, or work in characteristic zero. Unless $G$ is an affine polynomial head, it has at most $m+4mn/(t-d)$ witnessed scalars. This includes rational generic sections having poles at finite $X$.

Write the root as $B(X)/A(X)$ with $A,B$ coprime over the parameter function field and the denominator monic. Let $L$ be generated over $k(Z)$ by all their coefficients. Its conjugates correspond exactly to the conjugates of the rational function because the representation is unique. More explicitly, over the separable closure the distinct conjugates form an orbit of size $b$. The coefficients actually belong to that separable closure: extending constants purely inseparably preserves irreducibility of every separable factor in $Y$, so each rational root after that extension was already rational over the separably closed constants. Thus $[L:k(Z)]=b$ and $L(X)=k(X)(Z,B/A)$. Let $C$ be the smooth projective curve of $L$.

The coefficients of $A,ZA,B$ span a linear system on $C$. At each place subtract the minimum valuation of these coefficients, i.e. choose the divisor of poles that makes the system have no common base point. Its degree is $m$. To verify this, take the three sections $A(X),ZA(X),B(X)$ over the independent field $k(X)$. At a constant place they have no common zero because of the choice of minimum valuation and independence of $X$. Any further common zero on $C_{\,\overline{k(X)}}$ would trace a curve in $C\times\mathbb P^1_X$ dominating $C$. Over the generic point of $C$ it gives a common root of the coprime $A,B$ in $\overline{L}$. The three sections consequently define a morphism to the projective scalar/value plane. It is birational to the projective plane curve of $G$ by $L(X)=k(X)(Z,B/A)$. Pulling back a generic line gives the asserted degree. In particular every nonzero section in this system has at most $m$ zeros, including its base-divisor normalization.

Each witnessed point $(\gamma,f_\gamma)$ on the plane curve over $k(X)$ has a lift on the smooth model after extending scalars to $\overline{k(X)}$, by surjectivity of normalization. Since its $Z$ coordinate is a finite constant and $Z:C\to\mathbb P^1$ is finite, this lift is a constant point of $C$ over $\gamma$. The projective coordinate $A(X)$ at the lift is nonzero since the point has finite scalar and ordinate. The identity $B(X)=f_\gamma A(X)$ at the lift specializes to all physical sites, permitting zeros of both sides.

At any fixed $x$, $A(x)$ and $B(x)$ do not both vanish identically on $C$ by their coprimality in $L[X]$. The section $B(x)-u_0(x)A(x)-u_1(x)(ZA)(x)$ thus gives the two incidence bounds used above with $c=m$. When the section is nonzero at most $m$ labels agree. When it vanishes identically every failure costs a zero of the nonzero $A(x)$. The same two-label and outside-label argument now gives $m+4mn/(t-d)$, without any discarded denominator specializations. Consequently a population exceeding this bound on an irreducible projected factor of ordinate degree at least two requires its generic cover over the algebraic closure of $k(Z)$ to have no rational section in $X$.

## Cubics whose discriminant is scalar modulo squares

Let $G=AY^3+BY^2+CY+D$ have total scalar/value degree $m$, and suppose its discriminant is $L(Z)W(X,Z)^2$ for squarefree $L$. This includes cyclic irreducible cubics. In characteristic zero, or characteristic exceeding $3$ and $3\deg_X G$, there are at most $\max(35,1+4n/(t-d))m$ witnessed scalars. At the named half-rate pivot this is at most the preceding quadratic price $(2+8n/(t-d))m$. The shared plane-degree budget therefore leaves the same **466,186,464** labels after these cubics are also counted. A remaining cubic must have at least one odd-multiplicity discriminant factor of positive $X$-degree.

Take the constant parameter curve $C_0$ with $S^2=L(Z)$, using the scalar line with a chosen constant square root when $L$ is constant. Its map to the scalar line has degree at most two. Put
\[
 U=B^2-3AC,\quad V_0=2B^3-9ABC+27A^2D,\quad
 R=(-V_0\pm 3A\sqrt{-3}\,W S)/2.
\]
Here $V_0^2-4U^3=-27A^2\operatorname{Disc}_YG$. The two choices for $R$ have product $U^3$. Choose one nonzero as a polynomial in $X$ over $k(C_0)$. For any cube root $J^3=R$, the expression $J+U/J$ solves $T^3-3UT+V_0=0$, which becomes the original cubic under $T=3AY+B$. Conversely, if the cubic splits, let $T_1,T_2,T_3$ be the three transformed roots. For a primitive cube root of unity $\zeta$, the two Fourier sums $(T_1+\zeta T_2+\zeta^2 T_3)/3$ and $(T_1+\zeta^2 T_2+\zeta T_3)/3$ have product $U$ and their cubes are precisely the two displayed values of $R$.

Exclude the at most $5m$ scalars where $A(X,\gamma)$ or the discriminant vanishes identically. This uses $\deg_ZA\le m-3$ and $\deg_Z\Delta\le4m-6$. At any other witnessed scalar the specialized cubic splits over $k(X)$, since it has a rational root and its nonzero discriminant is a square in $k(X)$. Take a constant point of $C_0$ over each such scalar. Its $R$ is a cube by the preceding formulas. Every coefficient of $R$ as an $X$-polynomial is regular over finite $Z$ and has pole divisor bounded by $(3m-6)(Z)_\infty$: the three coefficient products in $V_0$ have scalar degree at most $3m-6$, and $WS$ has scalar pole order at most $2m-3$ per unit pole of $Z$. Hence the leading $X$-coefficient vanishes at at most $6m$ chosen points. Remove these too.

Make $R$ monic over $k(C_0)$ and let $P$ be the product of its distinct monic irreducible $X$-factors whose multiplicities are nonzero modulo three. If $P=1$, the original $R$ is a cube times a parameter function. Adjoining a cube root of that function to the constants of $X$ thus produces a rational generic root of $G$, covered by the preceding section.

Otherwise put $h=\deg_XP$. For a monic polynomial over $k(C_0)$ its height is the sum, over places, of the largest pole order of its coefficients, including zero. These heights add on products by multiplicativity of the Gauss valuation. The height of the monic normalization of $R$ is at most $6m$. Indeed for the original unnormalized coefficient vector it is minus the sum of its minimum valuations; the poles lie in the fixed coefficient divisor above and the leading coefficient has principal divisor of degree zero. Thus $P$ has height at most $6m$. At every retained finite place the monic factors specialize integrally with full $X$-degrees: the leading coefficient is a unit, and multiplicativity of the local monic heights bounds each factor's poles by zero there.

At such a place $P$ can have no simple specialized $X$-root. A simple root would come from exactly one factor, with order one, whose multiplicity in $R$ is nonzero modulo three. All omitted factors have multiplicities divisible by three and preserve that nonzero residue even if their roots meet this one. This would contradict the cube specialization. Therefore at least $h/2$ units of vanishing of the nonzero $\operatorname{Res}_X(P,P_X)$ are charged to each retained place. Degrees of $X$-factors are below the characteristic under the hypothesis. The resultant's pole degree is at most $(2h-1)6m$ by its coefficient determinant. There are at most $24m$ retained places, in addition to the $5m+6m$ earlier exclusions. This gives the stated bound.
