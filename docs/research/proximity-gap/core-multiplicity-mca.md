# Second-prime MCA safety from received-line multiplicities

On every injective evaluation domain of length $n=2^{30}$ over the second named prime, MCA is safe through **313,250,000 errors at half rate** and **534,425,000 errors at quarter rate**, at every positive interleaving width. The gains over the previous safety bounds are 16,000 and 100,000 errors. At width two the three-surface bounds on the numbers of bad scalars are 2,145,073,115 and 2,145,262,823, both below $2n$. Width stability gives the stated result. The first failing error counts still require matching attacks. [Previous bounds and factor assignment](shared-factor-degrees.md) · [Width stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

## Choosing the interpolation surfaces after finding the heads

Write $e$ for the error count, $t=n-e$, $d=k-1$, $K=500000$, $\ell=1+\lfloor e/K\rfloor$ and $C=t-\ell$. Fix one witness polynomial $q_z$ of degree at most $d$ for each bad scalar $z$ and choose $t$ agreement sites. A polynomial head $a(X)+Zb(X)$, with both coefficient degrees at most $d$, is rich if it contains more than $K$ selected witnesses. Every rich head has core size between $C$ and $t-1$. Indeed, away from its joint core each site belongs to at most one of its scalar sections, so a population $L$ pays $(L-1)(t-c)\le e$ for core size $c$. A joint core of size $t$ would explain the original received pair on $t$ sites, which excludes a bad scalar. Different heads have at most $d$ common core sites and share at most one selected scalar section. [Affine-head counts](quarter-transverse-tangents.md)

First build the ordinary primary surface in row $h=0$ below. Its scalar/ordinate degree is at most $K$, so substitution at a rich head forces identical vanishing. In particular the rich heads are finite in number $j$, at most the ordinary primary ordinate degree. Crop the cores to $C$ sites each. Cauchy–Schwarz on the site multiplicities gives $jC^2\le n(C+(j-1)d)$ for $j>0$. In the remaining argument take $h=\min(j,5)$ rich heads arbitrarily and count their **full** core multiplicity $o_x$ at each site.

For an indicated primary or companion row with order $r$, plane degree $s$ and drop $u$, take
$$
 w=rt-hud,\qquad v=\lfloor(w-1)/d\rfloor,\qquad r_x=r-u o_x .
$$
The entries in each vector of plane degrees are indexed by $h=0,\ldots,5$. The drop is zero at $h=0$; the other rows use the displayed value.

| Rate | Surface | $r$ | $u$ | Plane degrees |
|---|---|---:|---:|---|
| $1/2$ | primary | 90 | 1 | 266426, 260278, 254455, 248957, 243779, 238921 |
| $1/2$ | companion | 174 | 2 | 15258, 15019, 14796, 14589, 14400, 14227 |
| $1/4$ | primary | 55 | 1 | 181766, 176938, 172281, 167795, 163477, 159325 |
| $1/4$ | companion | 108 | 2 | 8175, 8028, 7886, 7750, 7619, 7494 |

Use monomials $X^iY^aZ^b$ with $a\le v$, $a+b\le s$, $i+da<w$. Set the mixed jets in $X,Y$ of total order below $r_x$ equal to zero on the received line at $x$, as identities in $Z$. The number of columns is $\sum_{a=0}^v(s+1-a)(w-ad)$. With $J(r)=\sum_{a<r}(r-a)(s+1-a)$, the row count is at most
$$
 nJ(r)-hC[J(r)-J(r-u)]+\binom h2d\,u^2(s+1).
$$
The verifier checks $J(r-uo)+o[J(r)-J(r-u)]\le J(r)+\binom o2u^2(s+1)$ for every $0\le o\le h$, then uses the single and pair core counts. Every one of the 24 systems has a strict column surplus. On a selected section outside the $h$ chosen heads, at most $d$ agreement sites lie in each such head's core. The specialized polynomial has degree below $w$ and vanishing multiplicity at least $\sum_{x\in T}r_x\ge w$ over its $t$ agreements. Hence it is identically zero. Each of the other $j-h$ rich heads has more than $K-h$ sections outside those first $h$, exceeding both conditioned plane degrees when $h>0$. It divides both surfaces. When $h=0$ the same conclusion uses the original cutoff directly. Remove one copy of each of these $j-h$ heads; denote the residual plane and ordinate degree caps by $s_1,v_1$ and $s_2,v_2$. [Mixed jets with variable order](quarter-core-weighted-jets.md)

## A multiplicity bound using every received line

For any nonzero factor $G$, let $b_G$ be its ordinate degree, $W_G$ its $(1,d)$ weight in $(X,Y)$, and $i_x(G)$ its order in the ideal of the received line at $x$. The integer
$$
 \Delta(G)=b_G(n-d)+W_G-\sum_x i_x(G)
$$
is additive on products and nonnegative, including for content or scalar-only factors. For nonnegativity, the coefficient of the highest power of $Y$ is a nonzero polynomial in $X,Z$ of $X$-degree at most $W_G-db_G$. Change variables locally from $Y$ to $Y-u_0(x)-Zu_1(x)$. Its highest coefficient stays the same, and it is divisible by $(X-x)^{(i_x(G)-b_G)_+}$. Sum these lower bounds over the grid. Additivity of the orders follows by expanding in the two local parameters and multiplying their lowest nonzero homogeneous terms over the integral domain of coefficients in $Z$.

For the primary shape write $v_0=\lfloor(w-1)/d\rfloor$ before removing the $j-h$ heads. Since $\sum_xo_x\le h(t-1)$ and each removed head has defect $n-c\ge e+1$, every residual factor satisfies
$$
 \Delta(G)\le D_*:=v_0(n-d)-re+hu(t-1-d)-1-(j-h)(e+1).
$$
Let $F$ be an active common nonlinear factor with actual values $b,m,W$ for ordinate degree, plane degree and weight. Give all rich heads priority in the witness assignment. If all sections assigned to $F$ vanish on its complementary cofactor in the companion after removing rich heads and all copies of $F$, the coprime resultant price is $(s_2+v_2)m$. Otherwise choose one which does not. In the full conditioned companion write $F^a G$ with $F\nmid G$. Its cofactor $G$ does not vanish on the chosen section, including any rich-head factors put back. Thus $\sum_T i_x(G)\le W_G$ while $\sum_T(ai_x(F)+i_x(G))\ge w_{\rm companion}$ and $aW+W_G<w_{\rm companion}$. Consequently $\sum_T i_x(F)\ge W+1$ and $bd\le W\le\min(w_{\rm primary}-(j-h)d-1,bt-1)$. [Cofactor argument](half-blowup-gauss-window.md#15-two-case-factor-assignment-and-monotonicity-of-blowuph)

Write $a_x=(i_x(F)-1)_+\le b$. Then $\sum_T a_x\ge W-t$ and $\sum_xa_x\ge W+E$ for $E=b(n-d)-D_*-n$. The published blow-up inequality allows rational weights $0\le\lambda_x\le a_x$, $\sum_x\lambda_x\le W$, and bounds pole height per unit of plane degree by
$$
 (6b+2)W-3b^2d-3\sum_x\lambda_x^2-2\sum_x\lambda_x.
$$
Use the earlier bound if $E<0$ or $bd<t$. Otherwise fill exactly $W$. Put $z=W-t$. If the capacity on $T$ is at least $W$, filling there gives squared mass at least $W^2/t\ge z^2/t+2z$. Otherwise use all $z+y$ available there, with $0\le y<t$. On the remaining $e$ sites there is capacity at least $t-y+E$. Fill their largest capacities first to mass $t-y$. For capacities at most $b$ and total $c$, greedy filling mass $M$ has squared mass at least $Mc/e-b^2/4$. Indeed the average original capacity of the units taken, weighted by their filled mass, is at least $c/e$ (a size-biased average of the largest capacities, bounded below by the full size-biased average). Only one partially filled capacity causes a loss, at most $b^2/4$. Thus total squared mass is at least
$$
 z^2/t + 2zy/t +(t-y)E/e-b^2/4
 \ \ge\ z^2/t+\min(2z,tE/e)-b^2/4 .
$$
The first group's contribution is already at least $z^2/t$. Relative to the previous integer pole-height bound we may therefore subtract $2t+3\max(0,\min(2(bd-t),\lfloor tE/e\rfloor)-\lceil b^2/4\rceil)$. This improvement is independent of the actual $W$. Consequently the previous monotonicity proof still allows evaluation at its stated upper bound. [Nef weights and intersection inequality](half-blowup-gauss-window.md#14-gauss-graph-intersection-bound-and-volume-excess-cancellation)

## Tangent determinants with fixed jets

In a tangent determinant of degree $s$ and local order $a$, fix $p=\min(j,3)$ polynomial heads, and all their two-variable Hasse evaluation rows of orders below $q$, where $pq\le s+1$ and $q\le a+1$. These $P=p\binom{q+1}{2}$ rows are independent over the coordinate function field. For any one head take a product of linear functions vanishing to order $q$ at all the others and nonzero there at the chosen head. Multiplication by this product is invertible on its truncated jet space; an arbitrary jet can be represented after division by a polynomial of degree at most $q-1$. Multiplying back gives degree at most $pq-1$. This proves simultaneous jet interpolation even for collinear heads.

Let $M=\binom{s+2}{2}$, $V=pq(q-1)(q+1)/3$, the sum of fixed derivative orders. In each full determinant an order-$i$ Hasse row reduces the global degree bound by $id$. At a site in the chosen $C$-subset of that head's core, a translated column of degree $j'$ in this row has order at least $j'-i$ when nonzero. Summing the column shortfalls below $a$ gives the same $\binom{a+2}{3}$ loss per site as for evaluations. Compared with $M$ ordinary rows the fixed rows therefore cost $aP\ell+V(C-d)$ in the determinant gap, leaving
$$
 D=aMt-\binom{a+2}{3}n-\frac{s(s+1)(s+2)}3d-aP\ell-V(C-d).
$$
There are $M-P$ variable rows. When $D>0$ discard variable rows of cost $a\ell_i+sc_i\ge D/(M-P)$. Every maximal minor extending the independent fixed rows by the other rows vanishes. Their joint row span is proper, so a nonzero degree-$s$ polynomial contains all remaining tangents. The previous reflexivity and sparse polar bounds apply for $m>s(s-1)$. With $H$ the pole-height bound per unit $m$ and $R=(2b-1)n$, the unit price including discarded and exceptional tangents is
$$
 4b-2+2sb+\left\lceil\frac{(M-P)(aR+sH)}{D}\right\rceil .
$$
This uses the same characteristic guards and the same finite levels as the previous shared-degree proof. The verifier minimizes over the admissible fixed multiplicities, including ordinary evaluations $q=1$, and also retains the triangle and transverse prices. [Tangent determinant argument](tangent-polar-windows.md) · [Sparse polar bound](half-sparse-gauss-window.md)

## Third interpolation surface

Choose another surface $A_3$ using the primary order $r$, drop $u$ and local jet constraints, this time with plane cap $s_3=1{,}000{,}000$. Take $v_3=v_0$ at half rate and $v_3=v_0-1$ at quarter rate. Write $R_3$ for the same row bound as in the first section evaluated at $s_3$, and $B_i=s_3+1-i$. Use the strict weight cap
$$
 w_3=\max\left(v_3d+1,1+\left\lfloor
 \frac{R_3+d\sum_{i=0}^{v_3} iB_i}{\sum_{i=0}^{v_3}B_i}
 \right\rfloor\right).
$$
All twelve auxiliary shapes satisfy $w_3\le rt-hud$ and have positive column surplus. Thus $A_3$ vanishes on every selected section outside the chosen heads. Its larger plane degree allows it to miss a rich head. No rich-head removal is used in $A_3$.

Fix an active common factor $F$ of the first two surfaces, with ordinate degree $b$ and plane degree $m$. If $F\mid A_3$, the bounds on $F$ gain two additional constraints
$$
 W\le w_3-1,\qquad \Delta(F)\le v_3(n-d)+w_3-1-nr+hu(t-1).
$$
Both follow from factor additivity and the auxiliary surface's jets. Intersect each constraint with the existing primary bound. If $F\nmid A_3$, their ordinate resultant is nonzero over the coordinate function field. It vanishes at every scalar assigned to $F$ and its scalar degree is at most $bs_3+v_3m$ by the Sylvester determinant.

Suppose the two-surface price for this factor is $Am+Bb$, and the price with the two additional constraints is $Xm+Yb$. The verifier uses the improvement when $b\le v_3$ and $v_3<X<A$. Set
$$
 Y'=\max\left(Y,B+\left\lceil \frac{(A-X)s_3}{X-v_3}\right\rceil\right).
$$
Then $Xm+Y'b$ covers both cases. If $(X-v_3)m\ge s_3b$, the resultant price is at most $Xm$. For smaller $m$ the original price is at most $Xm+Y'b$. This avoids a global assumption that the auxiliary surface shares all factors.

## Final allocation and verification

Use the shared-factor allocation with the residual degrees above. A residual polynomial affine head has at most $K$ selected sections unless it is one of the rich heads already charged. Charge at most $s_1$ for value-independent factors of the residual primary. For each active common nonlinear factor take the cheaper tangent price appropriate to its actual degree range, raised to the coprime fallback if necessary. The earlier linear majorant in both degrees and the residual resultant estimate apply verbatim, replacing the per-small-head price by $K$. If there is no active common nonlinear factor, the bound is $J_j+s_1+s_1v_2+v_1(s_2+K)+L s_2$, where $J_j$ is the rich-head union charge and $L=1+\lceil4n/(t-d)\rceil$. This handles every nonnegative possible count of rich heads. [Residual resultant, slopes and endpoint maximization](shared-factor-degrees.md)

Lean constructs the primary, companion and auxiliary interpolants in all 36 configurations from the two incidence bounds on the selected cores. It also checks the rational square-mass bound for a greedy fill and the interpolation between its endpoint bounds. The blow-up intersection, plane-curve duality and allocation arguments above are written proofs. [Kernel-checked interpolation and greedy estimates](../../../ArkLib/Research/ProximityGap/Frontier/CoreMultiplicityMCA.lean)

The exact integer verifier checks 8,001 nonempty nonlinear degree cases at half rate and 5,995 at quarter rate, alongside every empty case and each surface rank. The primary and companion alone give 2,145,128,427 and 2,145,437,223. The third surface saves 55,312 and 174,400 bad scalars respectively. Both versions reach their maxima at $(j,\max b)=(1,124)$ and $(3,105)$. It also tests rational partial fills on four-site examples. [Run the verifier](../../../scripts/probes/probe_core_multiplicity_mca.py)
