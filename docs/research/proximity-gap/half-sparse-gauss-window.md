# Sparse surface polars at half rate

For the second named prime, every length-$2^{30}$ injective domain and every positive interleaving width has first half-rate MCA failure at **312,800,001 errors or later**. At its predecessor the proof bounds the number of bad scalars by **2,115,023,520**, leaving **32,460,128** below budget. The upper bound on the designated subgroup is **387,740,104**. Lean checks the two production interpolants, the arithmetic of the geometric bounds and every factor-degree allocation. The sparse intersection and tangent-duality arguments below are written mathematics. [Lean certificates](../../../ArkLib/Research/ProximityGap/Frontier/HalfSparseGaussWindow.lean) · [Integer probe](../../../scripts/probes/probe_half_sparse_gauss_window.py) · [Upper witness](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTetrahedron.lean)

At **314,491,700** half-rate errors, a universal Lean theorem rules out a positive dimension surplus for every ordinary mixed-jet multiplicity and pair of degree cutoffs. [Exact limit of the rank argument](johnson-jet-room.md)

## Newton volume for the surface gradient

Use the normalized graph from the preceding surface proof. Its gradient hyperplane class is $L$, its projected slope class is $A$, and $H_Y$ denotes the class of a point in the ordinate coordinate. For a factor $F(X,Z,Y)$ with value degree $b$, total scalar/value degree $m$ and coordinate/value weight at most $W$ with value weight $d$, that proof gives
\[
 \sum_i c_i\le L\cdot H_Y+L\cdot A,\qquad L\cdot H_Y\le2Wm .
\]
Here $c_i$ are the finite pole degrees after the regular coordinate change, over the retained simple scalar sections. That change preserves the support inequalities $x+dy\le W$ and $z+y\le m$ on monomial exponents. The graph keeps its direction and slope defined at singular centers. [Normalized Gauss graph and the pole divisor](gauss-polar-section-heights.md)

For $L\cdot A$, intersect a general gradient hyperplane and a general slope point on the graph. Both systems are basepoint free. General pairs of cuts miss every fixed proper closed subset of dimension at most one, by incidence dimension. They give either the empty or a zero-dimensional intersection. We may therefore compute on the dense open where the graph projects isomorphically to the smooth hypersurface, both gradient coordinates are defined, and all three base coordinates are nonzero. A nonlinear irreducible factor cannot itself be one of the coordinate hypersurfaces. On this open the intersection is given by $F$ and two linear combinations of its partial derivatives. Their local lengths agree with the intersection multiplicities on the graph.

All three polynomials have exponent support in the same downward-closed polytope
\[
 0\le y\le b,\qquad 0\le x\le W-dy,\qquad 0\le z\le m-y .
\]
In particular $bd\le W$ and $b\le m$. The sparse Bézout bound for isolated torus zeros with multiplicity gives $L\cdot A$ at most six times its volume. Positive-dimensional base components away from the general graph cuts do not enter the count of isolated zeros. Equivalently, embed the torus by all the lattice monomials of this polytope. The unit and the three coordinate monomials are present. The three equations are hyperplane sections. The degree-$k$ part of its homogeneous coordinate ring is spanned by monomials with exponents in the $k$-fold dilation, so the degree of the projective torus closure is at most six times the volume by the leading term of the Hilbert polynomial. Projective Bézout bounds the isolated intersection multiplicities by that degree in any characteristic. [Philippon and Sombra, sparse intersection bounds](https://arxiv.org/abs/0709.3306)

Integrating the areas $(W-dy)(m-y)$ from zero to $b$ yields
\[
 L\cdot A\le 6bWm-3b^2(dm+W)+2db^3.
\]
As $2db^3\le3b^2W$, the resulting pole budget per unit of actual $m$ is
\[
 H_b=(6b+2)W-3b^2d,\qquad \sum_i c_i\le mH_b.
\]

## Subtracting the polar intersection at infinity

The primal plane curve over the coordinate function field has coordinates $[Z:Y:T]$. Its degree-$m$ homogeneous equation has $Y$-degree at most $b$. It vanishes to order at least $m-b$ at $O=[0:1:0]$, since the total degree in $Z,T$ of each monomial is at least $m-b$. Each first partial has order at least $m-b-1$ there when $m>b$. Let the curve of tangent directions obtained from a vanishing Veronese determinant have degree at most $s$. For $m>s(s-1)$, the established reflexivity argument ensures that its pullback by the gradient is relatively prime to the primal equation. Choose its actual homogeneous degree $s'\le s$. The substituted form has degree $s'(m-1)$ and order at least $s'(m-b-1)$ at $O$ when $m>b$. [Dual-degree test](tangent-polar-windows.md#which-curves-can-contain-the-tangents)

The local intersection of two plane curves with no common component is at least the product of their multiplicities. Removing the contribution at $O$ from plane Bézout leaves at most
\[
 s\left[m(m-1)-(m-b)(m-b-1)\right]
   =s b(2m-b-1)\le 2s b m
\]
affine cheap points. For $m=b$ the subtracted contribution is zero. Every retained scalar gives a distinct affine primal point, so this subtraction applies even when several points share a tangent. The same calculation applies to the fixed-point polar of degree one used on a line of tangent directions. [Bézout and intersection multiplicities, Chapters 3 and 5](https://www.math.lsa.umich.edu/~wfulton/CurveBook.pdf)

## Shared degrees at 312,800,000 errors

Set $n=2^{30}$, $d=n/2-1$, $e=312800000$, $t=n-e$, and $C=t-8192$. Use two mixed Hasse surfaces of shapes $(66,93,123104)$ and $(128,181,8245)$ on the received pair. Their respective dimension surpluses are **55,334,760** and **15,817,673,019**. Select one witnessing section per bad scalar and assign it to a primary factor. The scalar-only primary factors cost at most 123,104 labels. Collect the other primary factors coprime to the companion in a single primitive product. Their combined scalar labels cost at most the degree of its value resultant, $123104\cdot181+93\cdot8245=23048609$. [Single-resultant theorem and extraction proof](quarter-common-factor-degrees.md#one-resultant-and-one-total-degree)

A polynomial affine head carrying more than $H=123104$ assigned labels divides both surfaces by substitution. Since $8192H>e$, its core has at least $C$ sites, and its assigned mass is at most $e+1$. The $j$ rich heads take one unit of value degree and at least one unit of scalar/value degree each. When $j\ge3$, all are collinear since $3C>n+2d$. Set $a=\lfloor7j/10\rfloor$ and
\[
 u_j=\left\lceil\frac{2ajC-j(j-1)d}{a(a+1)}\right\rceil,
 \qquad U_j=\max\!\left(u_j,\left\lceil\frac{j C^2}{C+(j-1)d}\right\rceil\right).
\]
The head mass is at most $j(e+1)$, and also at most $jn-(j-1)U_j$ for $j\ge3$. Small polynomial heads cost at most $(93-j)H$. The nonaffine common linear factors cost at most $21(8245-j)$ by the identity-site argument, using $4n\le20(t-d)$. [Rich-head union and transverse count](quarter-transverse-tangents.md#cost-of-a-tangent-outside-the-common-line) · [Common linear factor test](quarter-common-factor-degrees.md#one-resultant-and-one-total-degree)

It remains to price the common nonlinear factors. The sum of their actual scalar/value degrees $m$ is at most $8245-j$. For an individual factor of value degree $2\le b\le93-j$, take $W=66t-1-jd$ in $H_b$ and set $R_b=(2b-1)n$. There are at most $(4b-2)m$ discarded labels, and the retained tangents have total missing regular agreements at most $mR_b$. The existing tame characteristic requirements hold on the designated field. [Regular-agreement estimate](logarithmic-section-heights.md#ordinary-differentiation-at-a-repeated-received-root)

For the triangle determinant use $p=\min(2,j)$ fixed rich heads. Its price per unit $m$ for the retained tangents is at most
\[
 2b+\left\lceil\frac{(3-p)(R_b+H_b)}{3t-n-2d-8192p}\right\rceil .
\]
With $j=0$, use also the degree-six, slope-five Veronese determinant when $b>30$, and the degree-eight, slope-seven determinant when $b>56$. In each case $m\ge b>s(s-1)$ ensures the dual-degree test. For $(s,a)=(6,5)$ or $(8,7)$, set $h=\binom{s+2}{2}$ and $D=ah t-\binom{a+2}{3}n-s(s+1)(s+2)d/3$. The per-unit price is at most $2sb+\lceil h(aR_b+sH_b)/D\rceil$. For $j\ge3$ use also the transverse price $2b+\lceil(R_b+H_b)/(t+u_j-n-d)\rceil$. Its denominator is positive for every such $j\le93$. [Fixed rows](half-core-weighted-jets.md#fixed-polynomial-rows-in-the-tangent-determinant) · [Veronese determinant](tangent-polar-windows.md#a-determinant-bound-for-the-tangents)

Take the smallest applicable retained price and add $4b-2$ for discarded sections. The finite allocation multiplies the largest price per unit by the shared budget $8245-j$ and adds the five other label classes. Its maximum is **2,115,023,520**, at $j=0$ and $b=93$, where the per-unit price is **252,302**. The estimate gives the same lower endpoint at every positive width by stability and covers earlier counts by monotonicity. [Positive-width stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)
