# Low geometric genus at the last second-prime predecessor

At $n=2^{30}$, $d=2^{26}-1$, $t=357913943$, any surviving irreducible cubic component covering all but a single affine head and 34 scalar exceptions must have total geometric genus at least **100633650**. The genus is that of the curve in **$(X,Y)$ over the scalar field $k(Z)$**, where $k$ is the algebraic closure of the production prime field. This conclusion allows one other head of size $n-t+1$. Only the integer inequalities have been executable-checked.

## A bound from the pole divisor

Let $F(X,Z,Y)$ be the primitive factor with $Y$-degree three and weight $W$ for $(X,Z,Y)$ of weights $(1,0,d)$. Let $C_i$ be the smooth normalizations of its geometric components over the algebraic closure of $k(Z)$, and $g=\sum_i g(C_i)$. The projection to $X$ has total degree three. Put $\partial=\partial/\partial Z$ holding $X$ fixed, and $D=\partial^2 y$ in the original function field. If $D=0$, the [inverse-derivative argument](second-prime-quartic-intrinsic.md#multiplicities-over-the-scalar-function-field) permits at most three labels. If $D\ne0$, its pullback to each component is nonzero because the map on the original function field is injective.

The following computations use separable constants for differentiation. Every relevant finite center lies among the fixed evaluation sites or among roots of the value-leading coefficient or the $Y$-discriminant. Their respective $X$-degrees are at most $W-3d$ and $4W-6d$, below the characteristic. The roots therefore lie in the separable closure of $k(Z)$. In particular no derivative on the perfect closure is required. Above a split center each branch is a tame extension of degree at most three of a complete Laurent-series field, with trivial residue extension over the separably closed constants. At a finite center $\alpha$, choose a branch parameter $u$ with $X=\alpha+u^e$, $1\le e\le3$. The same expansions give the corresponding orders after extending constants to the algebraic closure. Away from the finite bad centers the projection is étale and the implicit derivative has no pole on the affine chart. [Tame parameters](https://stacks.math.columbia.edu/tag/0EXW)

At a fixed received site $x$, this parameter has $\partial u=0$. Write $L_x=u_0(x)+Zu_1(x)$. On each branch through $(x,L_x)$, $\operatorname{ord}D\ge\operatorname{ord}(y-L_x)$, since $\partial^2L_x=0$ and coefficient differentiation preserves order. The multiplicity of that plane branch at the point is $\min(e,\operatorname{ord}(y-L_x))$, by taking a generic linear form in the two local variables. The sum of branch multiplicities is the plane-curve order $r_x$ of $F$ there. Consequently $\sum_xr_x$ is at most the total zero degree of $D$, equal to its total pole degree.

Here is a bound for those poles. The total pole degree of $y$ over all components is at most $W$, because the degree of the map to $y$ is at most $\deg_XF\le W$; components constant in $y$ contribute zero. The sum of the orders of finite-$X$ poles of $y$ is at most $W-3d$. Indeed, at a finite $X$-place the primitive coefficient vector of $F$ has valuation minimum zero. The Gauss valuation applied to its leading coefficient $a$ times the product of monic root factors gives the sum of the pole orders over this place as $\operatorname{ord}(a)$, counting the roots with their local degrees. Summing gives $\deg_Xa\le W-3d$.

At fixed $X$-centers, including infinity via $1/X$, the derivation preserves valuation lower bounds. At a moving finite center one has
\[
 \partial u=-\alpha' u^{1-e}/e .
\]
Each differentiation lowers the valuation by at most $e$. At a branch where $y$ is regular and $e\ge2$, applying two derivatives to the nonconstant terms of its power series produces pole order at most $2e-1\le3(e-1)$. The constant term has regular derivatives. At an unramified regular branch, twice differentiating a series in $X-\alpha$ preserves regularity, since the terms of degrees zero and one acquire no negative powers. At a branch where $y$ has a pole of order $a_P$, its new pole order is at most $a_P+2e\le a_P+2+3(e-1)$. Thus in addition to the original pole divisor we charge at most two per finite pole, and at most $3(e-1)$ per ramified branch. The tame Riemann–Hurwitz formula, summed over the components, gives $\sum_P(e_P-1)=2g+6-2\#\{C_i\}\le2g+4$. We obtain
\[
 \sum_xr_x\le W+2(W-3d)+3(2g+4)=3W-6d+6g+12 .
\]

## The terminal numbers with a second head

The [quartic and low-degree eliminations](second-prime-quartic-intrinsic.md) leave a cubic component and at most one other positive-value-degree factor. This residual factor is either a nonhead linear factor holding at most 184 labels, or an affine head holding at most $n-t+1$ bad labels. The parameter-only factors account for at most 34 labels. Thus
\[
 M=2n+1-(n-t+1)-34=n+t-34=1431655733
\]
labels on the cubic suffice. Put $h=2^{25}$, so $34h<M$. Using the entire weighted section space as in the quartic argument gives
\[
\begin{split}
D(h,t)-(h+1)n&=2251799041933257,\\
D(h-3,t-290805098)&=2251799041933350,\\
D(h-3,t-290805099)&=2251799008378920 .
\end{split}
\]
Therefore $W\le290805098$ and $\sum_x r_x\le469762128+6g$.

Use the [polynomial jet multipliers](second-prime-intrinsic-cubic.md#imposing-polynomial-jet-membership) with $\mu=2048$, $s=470000000$, and total $(Z,Y)$-degree bound 34 for $F$. If $R=\sum_x r_x\le1073564022$, take $\sum w_x\le\mu R$. The number of coefficients is $1033446311425544217726$. With $A=\binom{\mu+1}{2}$, the cost is at most $(s+1-34)\mu R+34nA=1033446311037629779968$. The surplus is $387914437758>0$. The resultant degree bound $3s+2(34-3)=1410000062$ is strictly below $M$. This excludes $g\le100633649$. The same numerical implication applies to any independent proof of $R\le1073564022$.

For example, with $g_{\rm pol}$ the generic polar gcd degree of the [persistent singularities calculation](second-prime-persistent-singularities.md), its result gives $5R\le2n+47W-78d-8g_{\rm pol}$. Writing $J=W-d$, every $g_{\rm pol}\ge3J-19462226$ suffices for the intrinsic contradiction uniformly in $3d\le W\le290805098$. Indeed the integer cutoff is $G(W)=\lceil(2n+47W-78d-5\cdot1073564022)/8\rceil$, and $3J-G(W)$ is minimized at the largest $W$, where it equals $19462226$. [Exact arithmetic](../../../scripts/probes/probe_second_prime_low_genus.py)
