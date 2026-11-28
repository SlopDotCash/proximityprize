# Quarter-rate safety from a logarithmic derivative

On the first named prime, every closed ball through **536,970,914 errors** at rate $1/4$ and length $n=2^{30}$ contains at most $n$ words. The first failing count is at least **536,970,915**. The result holds on every injective evaluation grid at every positive interleaving width. The previous safe count was 536,871,004. This is a written proof with an executable certificate for the finite comparisons. [Harmonic involution reduction](quarter-list-harmonic-involution.md) · [Exact checker](../../../scripts/probes/probe_quarter_harmonic_logarithm.py)

## Two horizontal sections

Put $d=n/4-1$, $t=2d-100000$, and $k$ equal to the algebraically closed scalarized coefficient field, of the named characteristic $p$. Work over $K=k(X)$. If the list exceeds $n$, the harmonic reduction produces at least $M=1046898267$ distinct polynomials $f$ of degree at most $d$ satisfying $A(X,f)+B(X,f)f'=0$. Here $A,B$ are coprime in $k[X,Y]$, their ordinate degrees are at most five and exactly four respectively, and their weights for $\operatorname{wt}(X,Y)=(1,d)$ are bounded by $D=5d+4000000$ and $E=4d+l$ respectively, with $l=4000001$. In particular $B(X,f)\ne0$. At most $T=5999835$ grid sites have radial order different from three. There are at least $G=1053742156$ good sites of order three with cubic Taylor coefficient $b_3(x)\ne0$. [Reduction and notation](quarter-list-harmonic-involution.md)

Write $Q=q_2Y^2+q_1Y+q_0$ for the primitive square root of the quartic Hessian after removal of its scalar factor, and put
$$
P=2q_2Y+q_1,\qquad \Delta=q_1^2-4q_2q_0,\qquad r=-q_1/(2q_2).
$$
The reduction gives $\operatorname{wt}(Q)\le3d+l$, $\Delta\ne0$, and
$$
\phi(Y)=r+\frac{\Delta}{2q_2P}.
$$
The involution commutes with $\delta=\partial_X-(A/B)\partial_Y$. At every good site with received value $y$, $q_2(x)\ne0$ and $Q(x,Y)=q_2(x)(Y-y)^2$. In particular $\Delta(x)=0$ and $r(x)=y$.

Infinity is a horizontal section: in the parameter $Z=1/Y$, $\delta Z=Z^2 A(X,1/Z)/B(X,1/Z)$ is regular and vanishes at $Z=0$. Conjugation by $\phi$ makes $r=\phi(\infty)$ horizontal and regular for the vector field, so $B(X,r)\ne0$ by coprimality. Equivalently $P$ divides $(B\partial_X-A\partial_Y)P$ in $K[Y]$. Discard the at most one word $f=r$. The remaining $z=\phi(f)$ are rational solutions. Their finite poles are supported on zeros of the leading coefficient $B_4$ of $B$. Indeed an actual pole of order $m$ has $1\le m\le\deg P(X,f)\le2d+l<p$, so $z'$ has pole order $m+1$. If $B_4(x)\ne0$, evaluation at $z$ gives $-A(X,z)/B(X,z)$ pole order at most $m$.

## A fixed exceptional set

For each finite $x\in k$, let $i_x$ be the sum of the intersection multiplicities of $A$ and $B$ over all finite ordinate values at $x$. Then
$$
\sum_x i_x\le I=4D+5E-20d.
$$
To see this, write $a=\deg_Y B=4$ and $b=\deg_Y A\le5$. In the Sylvester determinant every term has $a$ coefficients of $A$, $b$ coefficients of $B$ and total ordinate index $ab$. Its degree in $X$ is at most $aD+bE-dab\le I$, and coprimality makes the determinant nonzero. At any $x$, at least one of the two forms has nonzero specialization since $X-x$ cannot divide both. Make a constant projective change of the ordinate sending to infinity a point outside the zeros of this specialization. The homogeneous resultant changes by a nonzero constant. Over the local DVR $k[[X-x]]$ one form now has unit leading coefficient and can be made monic. Its quotient algebra is finite free over the DVR. The determinant of multiplication by the other polynomial in this algebra is the resultant up to a unit. The valuation is the length of its cokernel by elementary divisors. This finite-length algebra decomposes over its points in the special fiber, with each local length equal to the intersection multiplicity there. All original finite intersection points are counted because the new point at infinity is not a common zero. This also proves the inequality when there are several intersections over the same abscissa. The constant-degree case uses the same determinant of scalar multiplication. [Local lower bound at radial order three](linear-contact-quotient.md#a-contact-order-forces-a-plane-intersection)

Every order-three site contributes at least five at its received point. Give each such abscissa charge five and give the others zero. At most
$$
L=I-5(n-T)\le 65999160
$$
abscissas have $i_x$ strictly greater than their charge. Form a finite set $S$ from the union of the following four sets:

1. Grid sites that are not good.
2. Zeros of $\Delta$ away from the good sites and good sites where $\Delta$ has order at least two.
3. Zeros of $B_4$.
4. Abscissas with intersection length strictly greater than their charge.

The second count is at most $\deg\Delta-G$, since every good site already uses one zero. The weight of $Q$ gives $\deg\Delta\le4d+2l$, and $\deg B_4\le l$. Hence
$$
s=|S|\le(n-G)+(4d+2l-G)+l+L\le117998495 .
$$

For every remaining word set $W_f=B(X,f)/P(X,f)^2$. Both its finite zeros and its finite poles lie in $S$. First consider an abscissa outside $S$ that is not a grid site. A zero of $B(X,f)$ would be a common zero of $A$ and $B$ at the point $(x,f(x))$, exceeding its charge zero. If $P(X,f)$ vanished there, $\Delta(x)\ne0$ would force $q_2(x)\ne0$ and the formula for $\phi(f)$ would give a pole, contrary to $B_4(x)\ne0$.

At a grid site outside $S$, the discriminant has a simple zero, $B_4(x)q_2(x)\ne0$, and the total intersection length in the fiber is five, all at its received point. A word missing this point cannot have $B(X,f)(x)=0$, for that would give another intersection. This excludes a hit at the fourth root of the specialized quartic as well. The same word has $P(X,f)(x)\ne0$. For a word hitting the point, $P(X,f)$ vanishes simply: a zero of higher order would make $\phi(f)$ have a pole in the displayed formula.

It remains to show that $B(X,f)$ vanishes exactly twice at a hit. Write $U=X-x$, $V=Y-y$. The order-three condition gives the quadratic initial forms $B_2=U(aU+cV)$ and $A_2=-V(aU+cV)$. Here $c\ne0$. Indeed, in $B(X,y+V)=\sum b_i V^i$ one has $\operatorname{ord}_U(b_0,b_1,b_2)\ge(2,1,1)$ componentwise. If $c=0$, then $b_1=O(U^2)$ and the constant coefficient $8b_0b_2-3b_1^2$ of the Hessian $4BB_{YY}-3B_Y^2$ has order at least three. The scalar multiplying $Q^2$ is a unit at a good site, so $Q(X,y)=O(U^2)$. The translated linear coefficient of $Q$ vanishes at $x$, which would give $\operatorname{ord}_x\Delta\ge2$.

Suppose now that $B(X,f)$ vanished at least three times. With $v=f'(x)$ we would have $a+cv=0$. As $f$ is a solution, $A+f'B=(Y-f)J$ for a polynomial $J$. The quadratic initial form on the left is $-c(V-vU)^2$. Thus $J$ is smooth at the point with tangent $V=vU$. Both $Y=f$ and $J=0$ are graphs in $U$ with that tangent, so $B$ has intersection length at least three with each by its quadratic initial form. Intersection with their product adds the two lengths. Equivalently, in the local ring modulo $B$ the two factors are nonzero divisors, and the exact sequence for their product adds their lengths. This gives $i_x\ge6$, a contradiction. Ordinary multiplicity already gave order at least two, proving the assertion about $W_f$.

## A differential equation with too many distinct roots

Let $H_S=\prod_{x\in S}(X-x)$. Each nonzero $W_f$ is a rational function whose logarithmic derivative $W_f'/W_f$ is a sum of simple fractions with poles in $S$. This follows by factoring its numerator and denominator over $k$ and holds in the named characteristic. Consequently $H_SW_f'/W_f$ is a polynomial of degree at most $s-1$; for $s=0$ it is zero.

Put $D_0=B\partial_X-A\partial_Y$ and $W=B/P^2$. The logarithmic derivative of this observable in $K(Y)$ satisfies
$$
 H_S\frac{\delta W}{W}=\frac{N_0}{B^2},\qquad
 N_0=H_S\bigl(D_0B-2B(D_0P/P)\bigr).
$$
Horizontality of $r$ cancels $P$. The bounds $\deg_YD_0B\le8$ and $\deg_Y(D_0P/P)\le4$ imply $\deg_Y N_0\le8$. After $j$ differentiations the result is $N_j/B^{2j+2}$ with
$$
 N_{j+1}=B D_0N_j-(2j+2)N_j D_0B,\qquad \deg_Y N_j\le8(j+1).
$$
Since evaluation at each solution commutes with $\delta$, $N_s$ vanishes at every remaining $Y=f(X)$ in $K$.

This numerator is nonzero. Take a geometric root $\gamma$ of the squarefree quartic $B$ different from $r$; extend $\partial_X$ to its separable field. In the local parameter $Y-\gamma$, $W$ has a simple zero and $\delta(Y-\gamma)$ has a simple pole with nonzero leading coefficient by coprimality. Hence $H_S\delta W/W$ has pole order two. Each of the next $s$ derivatives increases its pole order by two, since the current pole order is nonzero modulo $p$ and the coefficient derivation contributes only smaller orders. The characteristic exceeds $2s+2$. Therefore
$$
 \deg_Y N_s\le 8(s+1)\le943987968 < M-1=1046898266 .
$$
The $M-1$ distinct surviving polynomials cannot all be its roots. This excludes the last harmonic factor and proves the closed-ball bound. The exact first failing count remains open.

Run the integer comparison and local intersection controls from the repository root.

```sh
python3 scripts/probes/probe_quarter_harmonic_logarithm.py
```

## The stronger endpoint at 538,320,914 errors

On the first prime at quarter rate, **538,320,914 errors are safe**. Put $t=2d-1450000$, use large-group threshold $L=250000$ in the preceding reductions, and write $M=n+1-L-b_0=1073491812$. For a candidate linear factor of weight $D$ in the remaining interval from $5d-1$ through $5d+58000000$, set $l=D-5d+1$, $E=4d+l$, and $Z=Z_{r,h,1}(D)$ at $r=230000000$, $h=\lfloor r/3\rfloor$. Thus $\sum o_x\ge Z$. All exclusions outside this interval, the primary surplus, and the ordinary and mixed Bézout comparisons are recomputed at the new $t,L$. [Exact comparisons](../../../scripts/probes/probe_quarter_first_rational_observable.py)

Use $I_0$ for the binary-quartic invariant of degree two, $J$ for its cubic invariant and $R_0=4D+5E-20d$ for the bound on total plane intersections. The preceding bound on the exceptional order count gives $J=0$ throughout the remaining interval. The repeated-root exclusions use the same arguments and are rechecked at each pair of endpoints. For a squarefree binary quartic (including a cubic with one root at infinity) its binary discriminant is $4I_0^3/27$ when $J=0$. This follows by covariance, checking the representative $Y^4-Z^4$. In ordinary coefficients its discriminant is a polynomial even when the leading coefficient vanishes. At local orders $o=0,\ldots,6$ the quartic discriminant vanishes to orders at least $0,0,1,3,7,12,18$, by its sixteen monomials. Consequently $\operatorname{ord}_x I_0\ge i(o)$, with
$$
 (i(0),\ldots,i(6))=(0,0,1,1,3,4,6).
$$
The degree caps here give $o\le6$. [Quartic discriminant monomials and coefficient orders](eighth-list-quartic-discriminant.md)

Let $b$ be the number of sites other than good order-three sites. Degeneration at an order-three site costs at least two zeros of $I_0$, one more than $i(3)$. On the seven orders the inequality $i(o)-\mathbf1_{o\ne3}\ge o-2$ holds. Therefore
$$
 b\le \#\{o_x\ne3\}+\deg I_0-\sum_x i(o_x)
   \le 4d+2l+2n-Z .
$$
This bounds $b$ already in the squarefree cubic case, and the previously constructed rational cubic root excludes it since $2(t-b)>3d+l$. In the remaining squarefree quartic, a polynomial word with $a$ good hits has reduced image denominator degree at most $2d+l-a$ and reduced numerator degree at most $3d+l-a$. At **every** good nonhit the unreduced denominator is a unit. Its image has at least $n-b-a$ good hits. Hence the symmetry proof requires only
$$
 3(n-b)+3(t-b)>D+12d+6l .
$$
This implies $3(n-b-a)>D+6(2d+l-a)$ because $a\ge t-b$.

For the logarithmic support, in the normalization $4BB_{YY}-3B_Y^2=C Q^2$ one has $C\,\operatorname{disc}(Q)=4I_0$. Both sides scale by the same fourth power of the linear-change determinant: the binary Hessian accounts for two powers and the quadratic discriminant accounts for two. Direct evaluation at $Y^4-Z^4$ gives the factor four, and homogeneity accounts for scalar factors of the quartic. In particular a zero of $\Delta$ is always a zero of $I_0$, with at least the same multiplicity.

At each grid site reserve $i(o)$ zeros of $I_0$ and $c(o)=(o^2-o-1)_+$ local intersections of $A,B$. At an order-three site these reserves are one and five. Any required exception there consumes either an extra zero of $I_0$, an extra intersection, or a zero of $B_4$, by the clean-site proof above. This includes degeneration, a multiple discriminant zero, an intersection at the other ordinate and the exceptional tangent. At another site with positive reserve, include the site in the support once. At a site with no reserve, including any other finite abscissa, both $B(X,f)$ and $P(X,f)$ are units unless $A,B$ intersect, $\Delta$ vanishes or $B_4$ vanishes. Each of these exceptions costs at least one of the unreserved degrees. It follows that the common finite support has cardinality at most
$$
 l+\deg I_0+R_0-\sum_x \big[c(o_x)+i(o_x)
       -\mathbf1_{o_x\ne3,\ c(o_x)+i(o_x)>0}\big]
 \ \le\ l+4d+2l+R_0+9n-5Z .
$$
The last inequality is the seven integer comparisons $c(o)+i(o)-\mathbf1_{o\ne3,\ c(o)+i(o)>0}\ge5o-9$.

The verifier splits the weights at degree changes and at offsets $2j\cdot1450000$ from $5d$. Twelve subintervals are excluded either by a negative upper bound for $\sum(o_x-3)^2$ or by the affine intersection bound $2jZ\le [j(j+1)+1]n+R_0$ for $j=2,3,4$. On the other ten subintervals it checks the inequalities at both endpoints. Bounds consisting of an affine function minus a positive multiple of $Z$ are convex, so their upper bounds hold on the entire interval. The minimum symmetry surplus is **7,374,761**. The maximum support bound is **113,875,580**, giving a logarithmic numerator of ordinate degree at most **911,004,648**. The required $M-1=1,073,491,811$ sections exceed that degree. This excludes an oversized list and establishes the first-failure floor **538,320,915**.
