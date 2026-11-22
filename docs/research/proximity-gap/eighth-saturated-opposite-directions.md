# A saturated quartet at 671,088,639 errors

Four noncollinear polynomial heads with the exceptional core sizes at this error count carry at most **2,113,929,217 distinct assigned bad scalars**. The other factors contribute at most **20,607,410**, giving at most **2,134,536,627** in this case against a budget of **2,147,483,648**. This eliminates the last quartet in the written safety proof at length $n=2^{30}$ and dimension $k=n/8$ over the second named prime. Its first failing error count is therefore at least **671,088,640**. [Complete allocation and verification scope](eighth-rich-head-safety.md) · [Lean direction and counting certificates](../../../ArkLib/Research/ProximityGap/Frontier/EighthSaturatedOppositeDirections.lean)

## Which sites can witness a fourth-head label?

Put $d=k-1$. Number the five-fresh head zero. Its core size is $3k-4$, and the other three core sizes are $3k$ each. Their sum is $n+4d$. Every triangle determinant is nonzero and has degree at most $2d$. At a coordinate in $j$ of a triangle's cores it vanishes to order at least $\max(0,j-1)$. Summing the four triangle bounds shows that every coordinate is covered by one or two cores. An uncovered site or a site in at least three cores would make the summed inequality strict. There are $4d$ double sites, and each triangle spends its entire $2d$ root budget. [Triangle multiplicities](../../../ArkLib/Research/ProximityGap/Frontier/_HalfPredecessorRateQuarterDeterminantMultiplicity.lean)

The triangle of the three large heads therefore contains $2d$ double sites. Outside the five-fresh head's core, every other site is a singleton owned by one of the three large heads. Their number is $n-(3k-4)-2d=3k+6$. The Lean declaration `layout` derives the cover and both counts from the individual triangle budgets. The declaration `face_budgets` supplies those budgets for the actual physical agreement masks of four polynomial heads.

## Two finite labels at a double site

At all $4d$ double sites two evaluated heads coincide. Each of the three quadratic minors with columns $1,A,B,A^2$, $1,A,B,AB$, or $1,A,B,B^2$ is proportional to the same monic double-site locator. Canceling the locator as a polynomial gives coefficients $a,b,c$ in the field with $b^2-ac\ne0$. For every pair of opposite sides $u,p$, the identity
\[
a u_2 p_2-b(u_1 p_2+u_2 p_1)+c u_1 p_1=0
\]
holds identically in the coordinate. It can now be evaluated at the roots of the locator. The discriminant is nonzero because the product of the four triangle determinants is nonzero. [Degree saturation and the discriminant](../../../ArkLib/Research/ProximityGap/Frontier/FourHeadCoreDeterminant.lean)

Suppose a fourth-head label $z$ uses a double site of the first three. Choose one owner for the side from the fourth head, and use the opposite side from the other owner to the remaining large head. Both owners equal the received pair. If the remaining head uses the site for a finite label $t$, then $u_1+zu_2=p_1+tp_2=0$. Both second-coordinate differences are nonzero, since a fresh folded agreement with equal second coordinates would also agree in the first coordinate. Substitution and cancellation give
\[
a+b(z+t)+czt=0.
\]
For fixed $z$ this determines at most one $t$. If $b+cz=0$, then $a+bz=0$ would force $b^2=ac$, so there is no finite partner. The argument applies to either orientation of the two sides. Global polynomial cancellation precedes evaluation throughout.

## Counting the lost first-three slots

Assign each distinct quartet label to one representing head. For the three large heads, choose one fresh site per assigned scalar. These choices occupy distinct pairs of a head and one of its off-core sites. There are at most $15k$ such pairs in total. Write $A$ for the number occupied.

Each of the $M$ labels assigned to the fourth head requires five distinct fresh sites because the agreement threshold is $3k+1$ and its core has $3k-4$ sites. A given off-core site can represent only one finite scalar for this head. Hence the chosen sites number $5M$. At least $5M-(3k+6)$ are first-three doubles. Each reserves the off-core slot of its remaining large head. Among all the reserved slots for one fourth-head label, at most one can be occupied by the global choice for the first three, since each would give the same finite partner. Thus
\[
 A\le15k,\qquad A+4M\le18k+6.
\]
Taking three copies of the first inequality and one copy of the second yields $4(A+M)\le63k+6$ and the stated integer bound. The Lean declaration `saturated_cap` invokes the polynomial direction theorem, proves uniqueness of the partner and bounds the actual intersection of the two finite slot sets. Its inputs include the selected fresh-site schedule. The global choice of heads and the remaining-factor bound come from the [full eighth-rate argument](eighth-rich-head-safety.md).
