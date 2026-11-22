# The first-prime quarter-rate successor is equivalent to a split polynomial pencil

Let $H$ be the subgroup of order $n=2^{30}$ in the first designated prime field. At quarter rate $k=268435456$, the first undecided error count is $e=447392428$. Write $d=k-1=268435455$, $t=n-e=626349396$ and $D=d-1=268435454$.

A received pair exceeds the budget of $n$ bad scalar labels **if and only if** there are coprime degree-$D$ polynomials $P,Q$ such that $P,Q,P-Q$ all have $D$ distinct roots in $H$. Equivalently, the three polynomials have degree $D$ and $PQ(P-Q)$ divides $X^n-1$. In the failure case the exact worst-pair count is **$n+2=1073741826$**. The existence of this pencil over the named positive-characteristic field remains open. [Lean equivalence and sharp failure mass](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitCriterion.lean) · [One uncovered site and three saturated intersections](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorOneHole.lean) · [Construction from the three fibers](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitPencil.lean) · [Single divisibility test](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitPencilProduct.lean) · [Named threshold and rank scan](../../../ArkLib/Research/ProximityGap/FirstPrimeQuarterPencilReview.lean)

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

A rational pullback realizing the three fibers has only four possible proper inner degrees. Every Galois inner cover has degree at most two. [Source symmetries and the collision-curve bound](quarter-split-pencil-pullbacks.md)

## Ramification at zero and infinity

Let $e_0,e_\infty$ be the ramification indices at zero and infinity of the rational map defined by a candidate pencil. Every candidate at the first designated prime satisfies
\[
 e_0+e_\infty\le100527252.
\]
Thus the lowest degree of a nonzero member is at least **167,908,203**. More generally, if the smallest and largest exponents of a nonzero member are $u,v$, then $v-u\ge167908202$. These restrictions apply without assuming a pullback, an involution, or an occupied coset. They leave the existence of a pencil with small ramification open.

Write each full fiber as a monic vanisher. Since the pencil has degree $D$ and no base point, the unique member over the value of the map at infinity has degree $D-e_\infty$. Differences of the three monic vanishers are scalar multiples of this member. Their coefficients in degrees $D-1$ through $D-e_\infty+1$ therefore agree. The monic polynomials on the reciprocal root sets have the same property at infinity with index $e_0$: replace each vanisher $F$ by $X^DF(1/X)/F(0)$. By Newton's identities, the three root sets have identical power sums at positive exponents $s<e_\infty$ and negative exponents $-s$, $0<s<e_0$. All these exponents are distinct modulo $n$ since both indices are at most $D<n/2$. [Lean coefficient and Newton identities](../../../ArkLib/Research/ProximityGap/Frontier/SplitFiberNewton.lean)

Fix a generator $g$ of $H$. For two colors $A,B$, let $b_j=1_A(g^j)-1_B(g^j)$ and $a_j=b_j-b_{j+n/2}$ for $0\le j<n/2$. At an odd exponent $s$ the difference of their power sums is $\sum_j a_j(g^s)^j$. For $m=2^k$ and any nonzero integral vector $a$ of length $m$, let $N$ be the determinant of multiplication by $\sum_j a_jX^j$ modulo $X^m+1$ in the monomial basis. This determinant is nonzero by irreducibility over $\mathbb Q$. Its rows are signed rotations of $a$, hence $N^2\le(\sum_j a_j^2)^m$. If the polynomial vanishes at $z$ distinct roots of $X^m+1$ modulo $p$, the independent Vandermonde columns at those roots give $p^z\mid N$ (equivalently, use Smith normal form). Thus $p^{2z}>(\sum_j a_j^2)^m$ forces $a=0$. [Lean determinant and divisibility proof](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFoldedNorm.lean)

For the three possible pairs of colors, the three local squares sum to at most three times the number of occupied sites in each antipodal pair. This follows by separating the cases of zero, one, or two occupied sites, including equal colors. Some pair thus has energy at most $3D=805306362$. If $e_0+e_\infty>100527252$, there are at least $\lfloor e_0/2\rfloor+\lfloor e_\infty/2\rfloor\ge50263626$ odd test exponents. At $p\ge2^{158}$ one has
\[
805306362^{268435456}<p^{50263626}.
\]
Taking $m=n/2$ proves that $a=0$. Each of the selected colors is stable under negation because their disjoint signed indicator takes the three values $-1,0,1$.

Square the roots of these two colors and take their images in the group of order $n/2$. Their sizes are both $D/2=134217727$, an odd number. Exponents congruent to $2$ modulo $4$ in the original intervals become odd exponents on this group. They give equal moments of the images, since their original power sums are twice those of the images. There are at least $\lfloor e_0/4\rfloor+\lfloor e_\infty/4\rfloor\ge24634900$ such tests. For this fixed pair the new folded energy is at most $4(D/2)=536870908$, using $(b_j-b_{j+n/4})^2\le 2(b_j^2+b_{j+n/4}^2)$. Since $536870908^{134217728}<p^{24634900}$, the same determinant bound gives another negation symmetry. An odd-sized subset of this even-order subgroup cannot be negation-stable. This proves the claim. The degree and exponent consequences follow from $e_0\ge1$, $u\le e_0$ and $D-v\le e_\infty$.

For a candidate which already factors through $X^2$, the three full fibers descend to odd size, so the three-pair average gives the smaller second-level energy $402653181$. The quotient ramification indices are $e_0/2,e_\infty/2$. At least 24,282,334 odd tests would again force an odd fiber to be stable. Consequently $e_0+e_\infty\le97129336$ for this subcase. The Lean results cover the folded norm, energy selection, contradiction from the two moment populations and exact integer comparisons. The Lean Newton theorem gives the positive and reciprocal power sums from the degree drops. The identifications of those drops with ramification and of the frequency intervals with the two node sets are given above. An independent finite check enumerates all 216 degree-two and 86 degree-three split triples through a fixed fiber in $\mathbb F_{17}$ and reproduces the three production norm certificates. [Lean moment obstruction and integer thresholds](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitRamification.lean) · [Finite verification](../../../scripts/probes/probe_quarter_split_ramification.py)
