# Bounding tangent poles on the surface Gauss graph

On the second named prime, every injective domain of length $2^{30}$ and every positive interleaving width has first half-rate MCA failure at **312,250,001 errors or later**. At the predecessor the bound on bad scalars is **2,131,191,599**, leaving **16,292,049** below the budget. The resulting lower endpoint improves the preceding 310,285,001 bound by 1,965,000 errors. The geometric ingredient below bounds the sum of the pole degrees of the rational tangents by $(6b+2)Wm$. Lean checks the section slope, both actual interpolation surfaces, the numerical hypotheses and the allocation. The intersection argument on the normalized surface and the regular-site argument are written mathematics. [Lean certificates](../../../ArkLib/Research/ProximityGap/Frontier/GaussPolarSectionHeights.lean) · [Exact integer probe](../../../scripts/probes/probe_gauss_polar_section_heights.py) · [Preceding half-rate proof](half-core-weighted-jets.md)

## A divisor that measures pole order

Work over an algebraically closed field $k$. Let $F(X,Z,Y)$ be irreducible with positive value degree $b$, coordinate degree at most $W$, and scalar degree at most $m$. Assume $F_Y$ is generically nonzero and the characteristic is zero or exceeds $2Wb$. Choose at most one polynomial section $q_i(X)$ for each of finitely many distinct scalars $z_i$. Require $F(X,z_i,q_i)=0$ and $\operatorname{Res}_Y(F,F_Y)(X,z_i)\ne0$ as a polynomial in $X$. These conditions ensure simple roots and exclude repeated components in the retained scalar fibers which dominate the $X$-line. For the velocity $V_i=-F_Z(X,z_i,q_i)/F_Y(X,z_i,q_i)$, let $c_i$ be the degree of its reduced denominator. A velocity identically zero has $c_i=0$.

Form the closure of the graph over $F=0$ of the gradient direction $[F_X:F_Y:F_Z]$ and its slope $[F_X:F_Y]$ in $(\mathbf P^1)^3\times\mathbf P^2\times\mathbf P^1$, and take its normalization $S$. The two target coordinates lie in the blow-up of $\mathbf P^2$ at $P=[0:0:1]$, given by the incidence equation for projection from $P$. The resulting morphism to that blow-up pulls back its exceptional line to an effective Cartier divisor $B$ on $S$. The generic gradient misses $P$ since $F_Y\ne0$. Denote the gradient hyperplane class by $L$, the slope point class by $A$, and the point classes of the three base coordinates by $H_X,H_Z,H_Y$. All five classes are nef, being pullbacks of globally generated line bundles. On the blow-up the lines through $P$ give $B+A\sim L$ after pullback.

At the generic point of each section, $F_Y\ne0$ makes the hypersurface smooth and the graph coordinates regular. The section lifts uniquely to $S$ and extends over each finite $X$ by properness. Its image there is a smooth graph, with inverse coordinate $X$. Differentiating $F(X,z_i,q_i)=0$ gives $F_X/F_Y=-q_i'$. Thus at every finite pole of $V_i$ both gradient coordinates relative to $F_Z$ are regular, and the slope has finite value. In this chart write $a=F_X/F_Y$, $v=F_Y/F_Z$. The gradient is $[av:v:1]$ and $B$ is cut out by $v=0$. On the section $v=-1/V_i$, so its intersection order with $B$ is exactly the pole order. This also handles points where all three partials vanish on the original hypersurface. No section under consideration is contained in $B$.

## Which curves can contain a pole?

Write $D=W H_X+m H_Z+b H_Y$. Homogenize each of the three partial derivatives to this common tridegree. On $S$ their tuple represents the gradient map and gives an effective divisor of class $D-L$. Indeed on each open where one target coordinate is a unit, divide its homogenized partial by that coordinate. These regular quotients agree by the graph identities and give the common factor as a global section of $D-L$. The same argument with the first two partials gives effective $D-A$. This works across the boundary of the original affine surface and its singular locus.

The map from $S$ to the original compactified hypersurface is birational. That hypersurface has multidegrees at most $(W,m,b)$. The product formula $H_XH_ZH_Y=1$ and the vanishing squares of the ambient point classes, with the projection formula, give the following bounds on $S$:
\[
 B\cdot H_Z\le L\cdot H_Z\le D\cdot H_Z\le 2Wb,\qquad
 B\cdot H_Y\le L\cdot H_Y\le 2Wm,\qquad
 B\cdot A\le L\cdot A\le D\cdot A\le D^2\le 6Wbm .
\]
Here each inequality with an effective difference follows by intersecting with a nef class. [Multiprojective degrees and intersection formulas](https://www.numdam.org/item/ASENS_2013_4_46_4_549_0/)

Take a component $E$ of $B$ meeting a selected pole. Its generic point lies in the affine chart with finite $X,Z,Y,a,v$. The function-field identity
\[
 dZ=-v(dY+a\,dX)
\]
holds there since $dF=0$. The normal surface is regular at the generic point of $E$ and smooth there over the perfect field $k$. Its module of differentials thus embeds in the rational differentials. Restricting the identity to $k(E)$ gives $dZ=0$. If $Z$ were nonconstant on $E$, its degree would be at most $B\cdot H_Z\le2Wb$. The extension of $k(Z)$ would be separable under the characteristic hypothesis, implying $dZ\ne0$ in $\Omega_{k(E)/k}$. Consequently $Z=z_i$ on each component through a pole of section $i$.

At the generic point of $E$ the graph identities give $F=F_Y=0$, including over original gradient base points, since $F_Y=vF_Z$ on this chart. If $X$ were nonconstant on $E$, its ordinate would therefore supply a common root over an extension of $k(X)$ at this fixed scalar. The nonzero value resultant excludes that case. Both $X=x_E$ and $Z=z_i$ are constant on $E$. The normalization is finite over the graph, so at least one of $Y,a$ varies on $E$. This includes curves above one fixed point of the original hypersurface, on which the slope must vary.

## Counting multiplicities at singular centers

At the poles of section $i$ use the equation
\[
 h_i=Y-q_i(X)+\lambda\bigl(a+q_i'(X)\bigr).
\]
It vanishes on its lifted graph $\Gamma_i$. A single $\lambda\in k$ can be chosen so that $h_i$ is nonzero on the generic points of all components of $B$ through these poles. Each such component has $X=x_E$, and at least one of $Y,a$ varies. Hence its equation becomes a nonzero affine linear combination of $Y,a,1$ there. On the normalization of its projective closure, the total order of its finite zeros is at most the sum of the degrees of $Y$ and $a$, by bounding its pole divisor. A nonzero constant has no zeros.

For clarity, at a pole let $R$ be the local ring of the normal surface. The functions $v,h_i$ form a system of parameters since they share no component there. A normal surface is Cohen–Macaulay, so their local intersection length is symmetric in the two equations. Calculated on the cycle of $h_i$, it is at least the pole order on $\Gamma_i$, which occurs in that cycle with multiplicity at least one. Calculated on the cycle of $v$, it is the sum, over components $E$ through the point, of their multiplicities in $B$ times the zero orders of $h_i$ on their normalized branches. These are the one-dimensional associativity formula for multiplicity and the degree formula on normalized curves. They allow the center on $S$ to be singular. [Intersection with effective Cartier divisors](https://stacks.math.columbia.edu/tag/0ER0)

Components charged for distinct $i$ have distinct constant coordinates $z_i$. Summing the preceding estimate over the finite pole points therefore gives
\[
 \sum_i c_i\ \le\ \sum_{E\subset B}\operatorname{mult}_E(B)
       (\deg_E Y+\deg_E a)
   =B\cdot(H_Y+A)\ \le\ (6b+2)Wm.
\]
The sum on the right can include all projective components, since their terms are nonnegative. This proves the height bound. For the agreement application use the existing coordinate change taking a regular fiber to infinity before this calculation. It preserves the coordinate weight and the polynomial sections and supplies numerator degrees at most $d+c_i$. [Coordinate change, excluded scalar fibers and regular-site counts](logarithmic-section-heights.md)

## Half-rate allocation

Take $n=2^{30}$, $d=n/2-1$, $e=312250000$ and $t=n-e$. The unconditioned mixed Hasse interpolants have shapes $(50,70,63277)$ and $(97,137,4712)$, and positive dimension surpluses $65,740,715$ and $4,690,383,112$. The two-surface resultant cutoff is $L_0=8,998,790$. Above it a value-linear factor is a polynomial affine head by the identity-site test, and has at least $C=t-\lfloor e/L_0\rfloor=761491790$ core sites. Three such heads are collinear since $3C>n+2d$. The usual union and fresh-site count bounds the mass of $j$ heads by $j(e+1)$, and also by $jn-(j-1)\lceil jC^2/(C+(j-1)d)\rceil$ when $j\ge3$. [Resultant and core allocation](tangent-polar-windows.md#from-components-to-all-received-pairs)

For $f$ total assigned value degree and $j$ rich heads, a remaining nonlinear factor of degree $b$ above cutoff divides both surfaces. Its upper coordinate weight is $W=50t-1-(f-b)d$ and its upper total scalar/value degree is $m=4712-j$. Put $G=(2b-2)m-b(b-1)$, $H=(6b+2)Wm$ and $R=(G+m)n$. The published regularity argument discards at most $G+2bm$ sections and bounds by $R$ the total number of missing regular agreements among the retained sections. It discards the entire scalar fibers where the value resultant vanishes identically. The geometric bound above supplies $H$ as their total denominator budget.

Both the ordinary tangent comparison and the triangle determinant with $a=\min(2,j)$ of the distinct rich heads apply. The discarded sections and the smaller of their two bounds give
\[
 G+2bm+\min\!\left\{
  \left\lfloor\frac{2tR+n(2H+mn)}{t^2-nd}\right\rfloor,
  \quad m(m-1)+\left\lfloor\frac{(3-a)(R+H)}{3t-n-2d-255a}\right\rfloor
 \right\}.
\]
Each fixed row has at most 255 missing agreements. The tangent argument also requires tame characteristic for its branch and dual degrees. All required characteristic bounds lie below the second designated prime. [Ordinary tangent comparison](logarithmic-section-heights.md#ordinary-differentiation-at-a-repeated-received-root) · [Triangle determinant with fixed rows](half-core-weighted-jets.md#fixed-polynomial-rows-in-the-tangent-determinant)

For each part take the larger of $L_0$ and its nonlinear price, using $L_0$ for a residual linear part. Allocate $f-j$ residual degrees and add the head allowance and the primary scalar-only allowance of 63,277. The maximum, **2,131,191,599**, occurs at $f=70$, $j=6$, with 32 parts of degree two. The probe checks both the per-degree majorant and the exact partition recurrence. Monotonicity and interleaving invariance yield the claimed lower endpoint. The designated subgroup has a verified first-failure upper bound of **387,740,104**. [Upper witness](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTetrahedron.lean)
