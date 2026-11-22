# Half-rate safety through 310,285,000 errors

On the second named prime at length $n=2^{30}$ and dimension $k=n/2$, every injective domain and every positive interleaving width has first MCA failure at **310,285,001 errors or later**. At 310,285,000 errors the written proof bounds the number of bad scalars by **2,101,754,336**, leaving **45,729,312** below the 128-bit budget. This raises the preceding tangent-polar lower bound by 485,000 errors. Lean checks the mixed interpolants under the two ownership counts, the rational triangle determinant, and the finite degree allocations. The passage from a nonlinear factor to its tangent heights and the plane-curve duality argument use the published written proofs. [Lean certificates](../../../ArkLib/Research/ProximityGap/Frontier/HalfCoreWeightedJets.lean) · [Independent exact enumeration](../../../scripts/probes/probe_half_core_weighted_jets.py) · [Preceding tangent-polar windows](tangent-polar-windows.md)

## Removing the rich affine heads

Put $d=k-1$, $e=310285000$, $t=n-e$ and $C=t-255$. Select one bad witness section $(z,q_z)$ per bad scalar. Use an unconditioned mixed Hasse surface of order 26, value degree 36, and total scalar/value degree 227608. Its positive dimension surplus is 2,142,924. Each selected section lies on this surface.

As long as a polynomial affine head $(A,B)$ of coordinate degrees at most $d$ carries more than $H=1+\lfloor e/256\rfloor=1212051$ remaining sections, remove all remaining sections with $q_z=A+zB$. Substitution into the unconditioned surface gives a polynomial in the scalar variable over the coordinate function field of degree at most 227608. More than $H$ distinct roots force the substitution to vanish identically. Thus $Y-A-ZB$ divides the surface. The removed heads are distinct, so their number $j$ is at most 36. The stopping rule leaves at most $H$ remaining labels on **every** polynomial affine head.

A head with core size $c<t$ and $m$ assigned labels obeys $(m-1)(t-c)\le e$. Since $e/H<256$, every removed head has at least $C$ physical core sites. Every head gives at most $e+1$ assigned labels. Distinct heads share at most $d$ core sites. For $j\ge3$, the inequality $3C>n+2d$ forces them all onto one line over the coordinate function field. The usual core-union bound then gives
\[
 U=\left\lceil\frac{jC^2}{C+(j-1)d}\right\rceil,\qquad
 A_j\le\min\{j(e+1),jn-(j-1)U\}.
\]
For $j<3$ use $A_j\le j(e+1)$. [Core and fresh-agreement counts](weighted-hodge-windows.md#joint-allocation-among-linear-and-nonlinear-factors)

## Two interpolants for the remaining sections

Take any $p=\min(j,6)$ removed heads. Write $m_x$ for the number of their cores containing the site $x$. For a shape $(r,v,s,u)$ use site order $r-u m_x$, value degree $v$, total scalar/value degree $s$, and strict coordinate weight
\[
 W_0=rt-pud.
\]
A remaining section differs from each chosen head specialized at its own scalar. On any agreement site which is also in that head's joint core, the difference polynomial vanishes. It has at most $d$ roots. Hence the sum of its site orders over its agreements is at least $W_0$. Both new surfaces contain every remaining section, irrespective of which factor supported it in the unconditioned surface. [Variable-order interpolation](quarter-core-weighted-jets.md)

Let $J_s(r)=\sum_{i=0}^{r-1}(r-i)(s+1-i)$. For each possible occupancy $0\le m\le p$, the mixed-jet row count satisfies
\[
 J_s(r-um)+m[J_s(r)-J_s(r-u)]
 \le J_s(r)+\binom m2 u^2(s+1).
\]
The single- and double-ownership sums satisfy $\sum m_x\ge pC$ and $\sum\binom{m_x}2\le\binom p2d$, by counting core sites and shared core sites. These yield the row budget for each of the fourteen surfaces. The scalar cutoff $L$ in the table is the maximum of $H$ and $1+s_1v_2+s_2v_1$ for the two residual surfaces.

| Conditioning heads | Primary $(r,v,s,u)$ | Companion $(r,v,s,u)$ | $L$ | Maximum labels, including removed heads |
| ---: | --- | --- | ---: | ---: |
| 0 | (26,36,227608,0) | (51,72,1355,0) | 16,436,557 | 2,101,754,336 |
| 1 | (26,35,209858,1) | (51,70,1284,2) | 14,735,001 | 1,940,269,525 |
| 2 | (26,34,195264,1) | (51,68,1229,2) | 13,319,739 | 1,336,432,924 |
| 3 | (26,33,183748,1) | (53,69,1190,2) | 12,717,883 | 1,564,625,816 |
| 4 | (26,32,175231,1) | (49,65,1164,1) | 11,427,264 | 1,806,506,453 |
| 5 | (26,31,169633,1) | (49,64,1128,1) | 10,891,481 | 1,862,193,428 |
| 6–36 | (26,30,166876,1) | (46,59,1097,1) | 9,878,595 | 1,811,710,971 |

Assign each remaining label to one irreducible factor of the new primary. Its factors independent of $Y$ cost at most $s_1$ labels in total. Every positive-value-degree factor with more than $L$ labels divides the new companion by the value-resultant bound. The identity-site test $t-\lfloor s_2n/L\rfloor-3\lfloor s_2n/(L-s_2)\rfloor>d$ holds in every row. A value-linear factor above $L$ would therefore be a polynomial affine head with more than $H$ remaining sections, contradicting the stopping rule. For a nonlinear factor of value degree $b$ among assigned factors of total value degree $f$, use $m\le s_2$ and coordinate weight $W\le W_0-1-(f-b)d$. [Resultant and identity-site test](hodge-section-variance.md#production-specialization)

## Fixed polynomial rows in the tangent determinant

Discard the published allowance $G+2bm$ with $G=(2b-2)m-b(b-1)$. Each remaining section determines a smooth point of the plane factor over the coordinate function field $K$ and a tangent head $(q_z-zV_z,V_z)$. Its common denominator has degree $c_z$ and the numerator degrees are at most $d+c_z$. At all but $\ell_z$ of the required agreements the denominator is a unit and the tangent equals the received pair. The height proof gives
\[
 \sum c_z\le C_0=2[(2b-2)W-b(b-1)d]G+2Wm,\qquad
 \sum\ell_z\le R=(G+m)n .
\]
These exceptions include the relevant finite branch incidences. The tangent line at the point over $K$ uses a nonzero value derivative in $K$. [Logarithmic height and regular-site proofs](logarithmic-section-heights.md)

When $p\ge1$, fix $a=\min(p,2)$ removed polynomial heads. Each has denominator one and at least $t-255$ good sites. For any three rows, clearing one denominator per row in the affine determinant gives degree at most $2d+\sum c_i$. At a site with $r_x$ good rows, subtracting one matching row from the others forces vanishing to order at least $\max(0,r_x-1)$. Consequently a nonzero determinant requires $3t-n-2d\le\sum_i(c_i+\ell_i)$.

Call a remaining tangent cheap when $(3-a)(c_z+\ell_z)<3t-n-2d-255a$. Every triple formed by the fixed rows and $3-a$ cheap rows has determinant zero. The fixed rows are independent in homogeneous coordinates, because two distinct affine points determine a line. Thus the cheap tangent points lie on a single line in the dual plane. This also holds with fewer than $3-a$ cheap rows. A nonlinear smooth plane branch has at most $m(m-1)$ distinct retained primal points whose tangent lines pass through a fixed projective point, by the polar intersection bound in the stated characteristic. The number of remaining labels, including the discarded ones, is at most
\[
 G+2bm+m(m-1)+
 \left\lfloor\frac{(3-a)(C_0+R)}{3t-n-2d-255a}\right\rfloor .
\]
This follows even if the fixed heads themselves are not tangents of the factor. [Polynomial matrix estimate and projective polar proof](tangent-polar-windows.md#a-determinant-bound-for-the-tangents)

When $p=0$, split at actual total scalar/value degree 240. Through 240 use the degree-one polar with three unfixed rows, evaluated at the upper bound 240. Above 240 use the published Veronese estimate with degree 16 and slope 14, evaluated at $m=s_2$. The dual curve cannot have degree at most 16 when the primal degree exceeds $16\cdot15=240$. The named characteristic exceeds all discriminant degrees and $m(m-1)$ in these applications. [Dual-degree test](tangent-polar-windows.md#which-curves-can-contain-the-tangents)

Finally, the total remaining value degree is at most $v_1$. For each total $f$ the Lean allocation checks every possible degree $b$ and its population per unit of value degree. The independent integer probe also evaluates the exact partition recurrence. The maximum occurs with no removed head and one factor of degree 36. Monotonicity covers all earlier error counts; interleaving stability gives the same safety statement at every positive width. [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityLedger.lean)
