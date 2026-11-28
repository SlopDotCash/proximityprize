# Singular first-derivative surfaces for folded Reed–Solomon witnesses

At the second-prime half- and quarter-rate Johnson pivots, a received pair with at least two MCA-bad labels has a nonzero interpolant whose **entire gradient in the scalar, value and derivative variables vanishes on every bad witness**. The two test radii are 314,491,699 and 536,870,913 errors. An overrun would put at least **2,101,215,370** half-rate or **2,128,018,540** quarter-rate labels on positive-dimensional components of the common singular locus of every such interpolant. There is also a sufficient safety test on an individual received pair. With two squarefree interpolants satisfying the coprimality test below, its numbers of bad labels are at most **60,193,734** and **61,648,290**, respectively. The sponsor budget is 2,147,483,648. An arbitrary pair may force a repeated derivative-dependent factor or a common factor after projection. Those cases keep both unrestricted endpoints open. First-derivative list and MCA bounds on arbitrary grids are due to Dao, Duke Kominers and Thaler. [DKT 2026](https://eprint.iacr.org/2026/2056) · [Earlier ordinary-interpolation obstruction](carbon-mcap2-pivot-rank.md)

## Interpolation at a moving received value

Put $n=2^{30}$, $d=k-1$ and $t=n-e$. Write $U_0,U_1$ for the degree-below-$n$ interpolants of the two received rows on the injective grid. In $F(X,Z,Y,V)$, $Z$ is the folding scalar, $Y$ the value and $V$ the first derivative. Use polynomials spanned by the monomials $X^iZ^aY^jV^\ell$ with $a+j+\ell\le S$, $\ell\le v$ and $i+dj+(d-1)\ell<W$. Write $\Delta=n-1-d$. The ordinary contact boards use $W=rt$ and the singular contact boards use $W=rt-\Delta$.

| Rate | Errors | Order $r$ | Derivative cap $v$ | Plane cap $S$ | Contact | Column surplus |
|---|---:|---:|---:|---:|---|---:|
| $1/2$ | 314,491,699 | 19 | 6 | 99 | ordinary | 4,128,454,092 |
| $1/4$ | 536,870,913 | 11 | 5 | 63 | ordinary | 17,888 |
| $1/2$ | 314,491,699 | 15 | 2 | 292 | ordinary | 1,603,007,627 |
| $1/4$ | 536,870,913 | 9 | 2 | 167 | ordinary | 1,610,623,611 |
| $1/2$ | 314,491,699 | 73 | 24 | 359 | singular | 459,712,885,250 |
| $1/4$ | 536,870,913 | 55 | 26 | 269 | singular | 729,614,679,390 |
| $1/2$ | 314,491,699 | 57 | 15 | 453 | singular | 193,772,302,476 |
| $1/4$ | 536,870,913 | 44 | 17 | 333 | singular | 285,082,020,609 |

At a site $x$ substitute $X=x+H$, $Y=U_0(x)+ZU_1(x)+HB$, $V=B+HC$ and require vanishing mod $H^r$ as an identity in $Z,B,C$. For an agreeing polynomial graph the substitution holds with $B=(q(x+H)-q(x))/H$ and $C=B'$. To count constraints, first translate $Y$ by the received affine function of $Z$, preserving total degree. For a fixed scalar power after translation, group terms by $b=i+j$ and $m=j+\ell$, where $i$ is the local exponent in $H$. The coefficients of $H^{b+h}B^{m-h}C^h$ from this block are linear combinations with weights $\binom{\ell}{h}$. Distinct triples $(b,m,h)$ give distinct output monomials. There are at most $\min(r-b,(\min(v,m)+1-(m-b)_+)_+)$ constraints per scalar power for $0\le b<r$, and at most $S-m+1$ scalar powers. These row counts and the strict monomial column counts give the displayed surpluses, hence a nonzero polynomial $F$. On any witness the specialized polynomial has its $t$ prescribed roots of order at least $r$ and degree below $rt$, so $F(X,z,q,q')=0$. [Kernel-checked integer counts](../../../ArkLib/Research/ProximityGap/Frontier/FoldedRadialMCA.lean) · [Independent Pascal-block checks](../../../scripts/probes/probe_folded_radial_mca.py)

## Why the gradient vanishes

Work on a singular contact board. First, $F_V(X,z,q,q')$ vanishes identically. In the local substitution, differentiation in $C$ gives $H F_V$, so $F_V$ has order at least $r-1$ on the same sites. Its specialized degree is below $rt-\Delta-(d-1)\le(r-1)t$, since $e\ge2$.

The two deformations
\[
 (z,q)\longmapsto(z+T,q+TU_1),\qquad
 (z,q)\longmapsto((1+T)z,(1+T)q-TU_0)
\]
preserve agreement on every original agreement site as polynomial identities in $T$. The coefficient of $T$ in either deformed interpolant therefore still has order at least $r$ there. Its coordinate degree is below $W+\Delta=rt$, since replacing one $Y$ by a received interpolant or one $V$ by its derivative increases its weight by at most $\Delta$. Both coefficients vanish. Suppressing the evaluation $(X,z,q,q')$, this gives
\[
 F_Z+U_1 F_Y+U'_1 F_V=0,\qquad
 zF_Z+(q-U_0)F_Y+(q'-U'_0)F_V=0 .
\]
Thus $(q-U_0-zU_1)F_Y=0$. If $q=U_0+zU_1$ identically, then the received fold at $z$ is a global codeword. On the witness support of any other scalar its codeword together with that global fold recovers a joint codeword pair by solving two scalar linear equations. There can therefore be no other bad scalar. With at least two, the prefactor is nonzero on every witness and all three partials vanish.

More generally reserving $L\Delta$ forces full multiplicity at least $L+1$ for $L<r$. Introduce independent parameters $\alpha,\beta,\gamma$ in the substitution
\[
 Z=z+\alpha,\quad
 Y=q+\alpha U_1+\beta(q-U_0-zU_1),\quad
 V=q'+\alpha U'_1+\beta(q'-U'_0-zU'_1)+\gamma .
\]
With $\gamma=0$ this is an agreeing graph on the original support. The coefficient of $\gamma^c$ has contact order at least $r-c$, by the Hasse derivative in the local variable $C$. Its subsequent coefficient at $\alpha^a\beta^b$ has weight below $W+(a+b)\Delta-c(d-1)\le(r-c)t$ whenever $a+b+c\le L$. All these coefficients vanish. At a bad witness the affine map in the three parameters has invertible linear part over the coordinate function field, with determinant $q-U_0-zU_1$.

The same rank condition separates logarithmic derivatives of residuals. If two nonzero residual polynomials $q-U_0-zU_1$ have equal logarithmic derivatives, their ratio is constant because their degrees are below the characteristic. Subtracting its constant multiple gives a nontrivial linear dependence of the two received rows modulo the code when the labels differ. Such dependence permits at most one bad label by the same two-equation argument (if the second row is already a codeword, none is bad). The Lean theorem checks distinctness under this quotient independence.

## A common singular component for the whole interpolation space

Work over $K=\overline{\mathbb F_p(X)}$. Take the common zero locus $\mathcal B\subset\mathbb A^3_{Z,Y,V}$ of a basis of the reserved interpolation space and all three first partials of its basis elements. Every bad point of a family of size at least two belongs to $\mathcal B$. The sum of the degrees of its irreducible components is at most $S^3$. To see this, start with affine three-space and cut by a generic linear combination of the defining equations. As soon as an irreducible component is contained in $\mathcal B$, retain it and cease cutting it. On all other components choose the next combination to be nonzero generically. Each proper cut increases the total degree by a factor of at most $S$ by Bézout, and lowers dimension by one. After three cuts each irreducible component of $\mathcal B$ is among the retained components or final points.

Put $\lambda=(V-U'_0-ZU'_1)/(Y-U_0-ZU_1)$. On each bad point $\lambda$ is defined and equals its residual logarithmic derivative. Both $Z$ and $\lambda$ distinguish the bad labels. A component where either is constant therefore contains at most one such label. A component contained in the pole-denominator locus contains none. At the half-rate pivot use $S=359$ and at quarter rate use $S=269$. Subtracting $S^3$ from $2n+1$ gives the bounds in the introduction on the number of labels on components on which both functions vary. In particular, a positive-dimensional common singular locus, independent of the choice of interpolant, is necessary for an overrun. A surface component of this locus would be a fixed repeated factor of every kernel polynomial, since the characteristic exceeds $S$.

There is a smaller degree budget for curves if no irreducible nonconstant factor divides the entire interpolation space over $K$. In that case choose two kernel elements with no common factor: take one first and then a linear combination outside the finitely many proper subspaces corresponding to its irreducible divisors. Intersect in the generic plane $Y=a+bZ$. The restrictions are coprime since the plane contains no component of their curve intersection. If their actual total degrees are $s_i$ and their degrees in $V$ are $v_i$, their homogenizations in $Z,V$ at $[0:1:0]$ have multiplicity at least $s_i-v_i$. Bézout leaves at most $s_1s_2-(s_1-v_1)(s_2-v_2)\le 2Sv-v^2$ affine intersections counted with multiplicity. At every point on a simultaneous singular curve the local intersection multiplicity is at least four. Count the distinct projected plane curves in $(Z,Y)$, discarding projected points. A generic line meets each projected curve in its degree many distinct points; each has a lift away from the finitely many omitted values. The sum of their degrees is consequently at most $\lfloor(2Sv-v^2)/4\rfloor$. This is **4,164** and **3,328** for the two smaller reserved boards. On the two narrower derivative boards the limits are **3,341** and **2,758**.

## Repeated surfaces and differential equations for the remaining curves

An overrun forces at least **2,115,451,893** half-rate or **2,134,768,350** quarter-rate bad labels on the following two loci together.

* One squarefree product $T$ of common fixed factors has derivative degree at most **two**, total degree in $(Y,V)$ at most **21** or **18**, and total degree in $(Z,Y,V)$ at most **99** or **63**, respectively. Each factor occurs at least twice in every reserved board polynomial used below.
* The other locus comprises curves projecting to equations $Q(Z,Y)=0$ on which the identity $Q_X+VQ_Y=0$ holds. Here $X$ is the independent coordinate, $Z$ is held constant, and the coefficients of $Q$ lie in $\mathbb F_p(X)$. Their reduced union of plane projections has degree at most **4,386** or **2,853**. Generically the derivative coordinate on each curve equals $-Q_X/Q_Y$.

Use the three boards with $(S,v)=(99,6),(292,2),(359,24)$ at half rate, or $(63,5),(167,2),(269,26)$ at quarter rate. The first two are ordinary and the third reserved. Over $K_0=\mathbb F_p(X)$ take the simultaneous zero set of bases of the three spaces and of the three partials of the reserved basis. Write $(s_0,v_0)$ for the bounds of the first board and $(S,v)$ for the third board. All equations have total degree at most $S$ and derivative degree at most $v$. Let $T$ be the product of the distinct common irreducible divisors of the equations. The common divisor can be computed over $K_0$ by polynomial gcd. Its geometric squarefree support descends to $K_0$, since a repeated purely inseparable factor would give degree at least $p$. The ordinary boards bound the degree of $T$ as in the first bullet, using $i+d(j+k)-k<W$ for the total $(Y,V)$ degree on the derivative-degree-two board. Because all the reserved first partials also vanish on $T$ and $S<p$, each geometrically irreducible component of $T$ occurs with multiplicity at least two in every reserved polynomial.

Off $T$, start with a nonzero equation from the first board and divide out every copy of factors supported on $T$, giving $F_0$. A generic linear combination $H$ of all equations shares no component with $F_0$. These two cuts yield a union of curves of total degree at most $s_0S$. Retain the irreducible curves in the common zero set. A third generic combination cuts all others properly. By Bézout, the sum of the degrees of the common components off $T$, counting isolated points as well as curves, is at most $s_0S^2$. In particular at most this many labels require an isolated point or a component where $Z$ or the residual logarithmic derivative is constant. If $F_0$ is constant the whole zero set off $T$ is empty.

On the normalization of a remaining projective curve $C$ put $h_{ZY}(C)$ equal to the pole degree of a generic affine linear form in $Z,Y$. This equals the sum over all places of the maximum of their two pole orders and zero. It counts the affine intersections with a generic vertical plane $Y=a+bZ$. Similarly $h_V(C)$ is the pole degree of $V$. Summing over the curves gives
\[
       \sum_C h_{ZY}(C)\le D:=s_0v+Sv_0-v_0v,\qquad
       \sum_C h_V(C)\le s_0S.
\]
For the first inequality restrict $F_0,H$ to the generic vertical plane. The homogenizations in $(Z,V)$ share the point $[0:1:0]$ to orders at least their actual total degrees minus their actual derivative degrees, using zero for a negative bound. Subtracting the product of these orders from the plane Bézout number gives at most $D$ affine intersections. This bound includes the degrees of the maps from the space curves to their plane images. The second inequality follows by cutting with a generic plane $V=c$. Each generic plane avoids the finitely many isolated intersections at infinity on each projective curve, apart from the fixed base points of its pencil, which contribute no poles to the generic fiber count.

The reduced union of the scalar-varying plane projections has a squarefree equation $Q(Z,Y)$ of degree at most $D$, with coefficients in $K_0$. For descent, pass to the generic scalar over $K_0(Z)$, remove $T$ and retain the simultaneous zero set there. Its points belong to the zero-dimensional intersection of $F_0,H$ in $(Y,V)$ of degree at most $s_0S<p$. Their residue extensions of $K_0(Z)$ are separable. Take the product of the distinct minimal polynomials of their $Y$ coordinates and clear denominators primitively in $K_0[Z]$. This gives the reduced union of the plane projections of all scalar-varying common curves. Including any with constant logarithmic derivative in this union preserves the bound by the same plane cut. No irreducible projected curve has identically vanishing $Q_Y$, by squarefreeness in $Y$.

At every bad witness on one of these curves, $Q(z,q)=0$ holds as a function of $X$, so differentiation gives $P=Q_X+VQ_Y=0$. On any curve where $P$ is nonzero it has at most $D h_{ZY}(C)+h_V(C)$ distinct affine zeros. Indeed this expression bounds the degree of its pole divisor, term by term. Such curves account for at most $D^2+s_0S$ labels. All other retained curves satisfy the asserted identity. Subtracting $s_0S^2+D^2+s_0S$ from $2n+1$ gives the two stated populations. This leaves both the fixed quadratic-derivative factors and the differential lifts as possible sources of an overrun. [Exact calculations](../../../scripts/probes/probe_folded_radial_mca.py)

## Projecting to the value and scalar

Treat $X$ as a coefficient by working over the algebraic closure of the coordinate function field. For a singular contact interpolant $F$, factor out its entire content $E(Y,Z)$ in $V$ and call its remaining primitive part $B(Y,Z,V)$. Suppose $B$ is squarefree as a polynomial in $V$ over $\overline{\mathbb F_p(X)}(Y,Z)$. Form the nonzero polynomial
\[
 R(Y,Z)=E(Y,Z)\operatorname{Res}_V(B,B_V)
\]
when $B$ has positive derivative degree; use $R=E$ when $B$ has degree zero in $V$. All witnesses lie on $R$ because $F=F_V=0$. As $\deg_V B\le v<p$, the resultant is nonzero under the squarefreeness hypothesis. Its Sylvester determinant gives total $(Y,Z)$ degree at most $(2v-1)S$ including the content, and ordinate degree at most $(2v-1)m$, with $m=\lfloor(W+v-1)/d\rfloor$. For example, the second bound uses $\deg_Y E+\deg_Y B\le m$ and the fact that each resultant term uses at most $2v-1$ coefficients. If the primitive part has repeated factors, the same projection applied to its squarefree product covers witnesses away from the repeated factors. Their distinct product has total degree at most $\lfloor S/2\rfloor$ and derivative degree at most $\lfloor v/2\rfloor$.

Now take two interpolants of the same singular board. If both primitive parts satisfy the hypothesis and their projections are coprime in $\overline{\mathbb F_p(X)}[Y,Z]$, the nonzero ordinate resultant bounds the distinct bad scalars by twice the product of the plane and ordinate caps. If both projections are independent of $Y$, no common zero is possible by coprimality; if only one is independent of $Y$, its own degree already bounds the labels. At half rate the $(r,v,S)=(57,15,453)$ board has projected caps $13137,2291$, giving $60193734$. At quarter rate the $(44,17,333)$ board gives $10989,2805$ and $61648290$. Positive rank alone does not imply the two coprime projections exist. The interpolation and projection arguments here are written proofs. Lean verifies the row and column arithmetic, gradient implication and residual Wronskian lemma. [Finite verifier](../../../scripts/probes/probe_folded_radial_mca.py)
