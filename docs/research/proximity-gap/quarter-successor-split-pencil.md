# The first-prime quarter-rate successor is equivalent to a split polynomial pencil

Let $H$ be the subgroup of order $n=2^{30}$ in the first designated prime field. At quarter rate $k=268435456$, the first undecided error count is $e=447392428$. Write $d=k-1=268435455$, $t=n-e=626349396$ and $D=d-1=268435454$.

At this error count Lean proves the following equivalence. A received pair exceeds the budget of $n$ bad scalar labels **if and only if** there are coprime degree-$D$ polynomials $P,Q$ such that $P,Q,P-Q$ all have $D$ distinct roots in $H$. Equivalently, each of $P,Q,P-Q$ has degree $D$, and $PQ(P-Q)$ divides $X^n-1$. In the failure case the exact worst-pair count is **$n+2=1073741826$**. The existence of this pencil over the named positive-characteristic field remains open. Lean checks the interpolation surplus, the numerical deficit and the sufficient construction from the three full pair fibers. The geometric necessity uses the written normalized-surface variance bound. [Lean certificate and construction](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitPencil.lean) · [Weighted section bound](weighted-hodge-windows.md) · [Previous exact probability](quarter-rate-two-rich-cores.md) [Geometric equivalence](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitCriterion.lean) · [Cyclic-domain divisibility equivalence](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitPencilProduct.lean)

Across 33,554,431 error counts beginning here, this same pencil controls the maximum relative to the line $n+6(e-447392428)$. [Interval theorem](quarter-collinear-interval.md)

## Forcing three affine heads

A selected bad label $z$ has a polynomial witness $q_z$ of degree at most $d$ agreeing with the folded row on at least $t$ sites, with no joint explanation on that support. Interpolate a surface $S(X,Z,Y)$ vanishing to order two, in the coordinate and value variables, on every received scalar line. Take total scalar/value degree at most 16, value degree at most three and coordinate/value weight strictly below $2t$, giving $X$ weight one and $Y$ weight $d$. The number of coefficients exceeds the $50n$ jet rows by **357913864**. Every selected section lies on the surface by double-root counting. [Double interpolation](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeQuarticInterpolation.lean)

Choose such a nonzero surface of minimal total scalar/value degree. No $Z-z$ divides it. Indeed dividing by this scalar-only factor reduces total degree, preserves the weight bound and preserves all three homogeneous jet equations. The value, coordinate derivative and value derivative on a received line are polynomials in $Z$. Each is divisible by the same $Z-z$ and each vanishes identically before division. On factoring over the algebraic closure, a factor of value degree zero therefore vanishes identically in $X$ for no selected scalar. All selected labels are accounted for by at most three distinct positive-value factors.

For an irreducible factor of value degree $b=2$ or $3$, its weight is at most $W=2t-1=1252698791$ and its total degree at most $m=16$. Apply the weighted section variance formula (1) at $K=81/100$. The two branch-degree bounds $(B_X,B_Z)$ are $(31,1968526673)$ and $(59,3400182435)$. They are strictly below the prime characteristic. The resulting population bounds, including the discarded sections, are respectively **27056** and **132662**. The characteristic and positivity conditions on $K$ hold in both cases. For a linear factor, 512 labels suffice to extract an actual secant using the identity-site incidence inequality with the current $t$. Each actual head has at most $e+1=447392429$ labels. Thus even two actual heads together with a small factor cannot exceed $n$ labels. An overrun needs three distinct actual heads, which exhaust the factor degree. [Variance formula and hypotheses](weighted-hodge-windows.md#weighting-by-the-fibre-degree) · [Secant extraction](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeLinearFactor.lean)

Assign every selected label to one of its heads. With total $L>n$, each population $L_i$ is at least $n+1-2(e+1)=178956967$. Write $C_i$ for the joint core of its polynomial row pair and $c_i=|C_i|$. Fresh agreements for distinct labels on one head use distinct sites, so $L_i\max(1,t-c_i)\le n-c_i$. It follows that every $c_i\ge t-2$. Three noncollinear polynomial row pairs have total core size at most $n+2d$. Here $3(t-2)>n+2d$, so the three heads are collinear over the rational-function field. [Three-core determinant](../../../ArkLib/Research/ProximityGap/Frontier/ThreeHeadDeterminantCover.lean)

## Seven units of slack

Write $E_{ij}$ for the sites where the two polynomial row pairs agree, irrespective of the received pair. Each has at most $d$ sites. Put $A=\sum_{i<j}(d-|E_{ij}|)$, and let $R$ count sites common to all three heads. Let $J$ be the number of fresh agreement incidences of the assigned labels, adding over sites and labels. Then
\[
  2\sum_i c_i+J\le 3n+2\sum_{i<j}|E_{ij}|-3R=3n+6d-2A-3R.
\]
At a covered site any fresh label cancels the common direction through its received head value. At most one distinct assigned label can do so. Three distinct head values contribute at most three to the left side. A coincident pair contributes at most five, and three coincident heads at most six. The same bounds hold at an uncovered site, where each distinct head value can give at most one label.

Put $u_i=\max(0,t-1-c_i)$. Each assigned label needs at least $1+u_i$ fresh agreements and $c_i\ge t-1-u_i$. The upper bound therefore gives
\[
  2A+3R+\sum_i(L_i-2)u_i\le3n+6d-6(t-1)-L\le7.
\]
All cores have size at least $t-1$. Their union has at least $3(t-1)-3d=n-4$ sites.

Write all three pair differences as polynomial multiples of a common primitive vector $(a,b)$. This follows by dividing one nonzero difference by the gcd of its entries and using collinearity and coprimality. Let $s=\max(\deg a,\deg b)$. If $s=0$, covered sites together give at most one fresh label, and the at most four uncovered sites give at most twelve more. Thus $s\ge1$. Coprimality ensures the primitive vector never vanishes in both entries at a site. Each multiplier has degree at most $d-s$, and $A\ge3s$.

Consequently $A=3$, $s=1$, $R=0$. Each pair coincides on exactly $D=d-1$ sites. The multiplier for that pair has degree $D$ and all its roots are distinct in $H$. Subtracting the first head from the other two gives multipliers $P,Q$ whose third difference is $P-Q$. No two share a root. The core union now has at least $3(t-1)-3D=n-1$ sites. If all sites were covered there would be no overrun. Hence there is exactly one uncovered site. It contributes at most three labels, and the covered sites give at most $n-1$, proving the upper bound $n+2$.

## A single hole realizes the overrun

Conversely, given such a pencil, use the three heads $(Xf,f)$ for $f=0,P,Q$. Each has degree below $k$. On the three disjoint full fibers receive the coincident head value. Of the remaining $n-3D=268435462$ sites set one aside. Split the rest into three classes of $89478487$ sites and at each site receive the corresponding head. Every head now has exactly $2D+89478487=t-1$ core sites.

At each covered site $x$ choose one foreign head with a different value. The scalar $-x$ gives a fresh agreement with that head. These $n-1$ ordinary labels are distinct. At the single remaining site the three head values are distinct. One may choose its received row pair off their common line, avoiding all three forbidden denominators and every direction used by an ordinary label. Fewer than $3n+6$ affine lines are excluded in a plane over a prime field of order greater than $3n+6$. The three fresh labels here are distinct from each other and from all ordinary labels. The prescribed core and its fresh site witness badness in each case. Any joint explanation agrees with the chosen head on $t-1\ge k$ sites and hence equals it, contradicting the fresh mismatch. This gives $n+2$ labels for one received pair.

Over the complex dyadic subgroup this degree lies strictly inside the proved full-fiber gap. The parity descent behind that result has a positive-characteristic proof for the 32-site quotient; its transfer to the full order-$2^{30}$ subgroup at this prime has yet to be shown. [Dyadic degree gap and its field hypothesis](quarter-three-heads-32-fibers.md#a-sharp-degree-gap-on-complex-dyadic-roots)

## Distance from the four standard cosets

Write $k=n/4$. Match the three root sets to any three distinct cosets of the subgroup of order $k$. If $v_i$ roots of the $i$th fiber are outside its assigned coset, that coset has $v_i+2$ holes. Write the respective polynomial as $(X^k-a_i)B_i/A_i$, incorporating its nonzero leading scalar into $B_i$. The roots of $A_i$ are the holes and those of $B_i$ are the extra sites. On clearing denominators in the relation among the three pencil members, each of the three coefficients $U_i=B_i\prod_{j\ne i}A_j$ has degree $v_1+v_2+v_3+4$. If this were less than $k$, separating the $X^k$ term would give $U_1-U_2-U_3=0$. At a hole of the first coset $U_1$ is nonzero and both other terms vanish. Therefore
\[
  v_1+v_2+v_3\ge k-4=268435452.
\]
Equivalently, **at most 536870910** of the roots can lie in their matched standard cosets, across all three fibers. The same leading-coefficient argument works when each template is a disjoint union of cosets of order $m$ with total size $k$. The template vanishers are monic in $X^m$, and $\sum v_i+4<m$ would again separate their highest power. [Lean polynomial separation](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitPencil.lean)

Even two distinct assigned cosets require $v_i+v_j\ge89478482$. The third fiber can use at most $v_i+v_j+4$ holes in these cosets. On either remaining standard coset, the equality of the first two polynomials is an equation between scalar multiples of $B_iA_j$ and $B_jA_i$. Both multiplying scalars are nonzero there. The two cleared polynomials are linearly independent by evaluating at a hole of the first coset. Their nonzero combination has degree at most $v_i+v_j+2$. Summing over both remaining cosets gives $k-2\le3(v_i+v_j)+8$.
