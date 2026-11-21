# First-prime quarter-rate safety at 447392427 errors

Let $n=1073741824$, $k=268435456$, $d=k-1$, $e=447392427$ and $t=n-e=626349397$. On every injective $n$-point evaluation domain over a finite field of characteristic greater than $2n$, every received pair has at most $n$ genuinely bad scalar labels at $e$ errors. The first designated prime has integer budget $n$. Its first failing error count therefore lies in **[447392428, 480946859]**. Lean proves the lower bound by counting the affine and nonlinear components of two interpolants. The subgroup attack at the upper bound is formalized in Lean. [Component estimates](three-rates-two-head-window.md#common-factors-and-the-remaining-intersections) · [Attack on the canonical code](../../../ArkLib/Research/ProximityGap/Frontier/_P1RateQuarterAdjacentExactPin.lean)

## Machine-checked range

On every injective length-$2^{30}$ domain in characteristic above 1968526676, the exact worst-pair numerator is $2(e+1)$ at all **44,739,244** error counts from **402653184** through **447392427**. The last numerator is **894784856**. On smooth domains over any finite field, the first failure is $\lfloor B/2\rfloor$ throughout the **89,478,488** integer budgets from **805306370** through **894784857**. This also gives the strict good real-radius interval at every positive width and the value returned by the support-rank search. For every smooth field with $q<2^{256}$, the field characteristic is at least 2013265921. This suffices because the quadratic discriminant has coordinate degree at most $2(w-d)=1968526676$ for $w=1252698793$ and $d=268435455$. Hence the entire error curve from zero through 447392427 holds at every positive width, throughout the sponsor’s field-size range. In particular the saturated step is good exactly when $B\ge894784856$. [Exact probability and first-prime bracket](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateTwoRichFloor.lean) · [All smooth finite fields and the rank search](../../../ArkLib/Research/ProximityGap/Frontier/SmoothQuarterTwoHeadWindow.lean)

For every integer budget from **0** through **894784857**, the first failure on a smooth domain is $\min(B,\max(402653184,\lfloor B/2\rfloor))$. Before the two-head interval, the worst-pair numerator equals $e+1$ for every $e<402653184$. The more general argument applies whenever $n=k+2a$, $2\le k<a$, over every finite field and on every injective evaluation domain. For every reciprocal-integer tolerance $1/Q$ and budget $B=\lfloor q/Q\rfloor\le 2a+1$, the first failure occurs at $\min(B,a)$. The proof combines an apolar count below the unique-decoding radius with the spike and two-head witnesses. [Field-independent probability and threshold](../../../ArkLib/Research/ProximityGap/Frontier/ApolarAllFieldPlateau.lean) · [Joined quarter-rate formula and exact rank result](../../../ArkLib/Research/ProximityGap/Frontier/SmoothQuarterTwoHeadWindow.lean)

At arbitrary real tolerance $\epsilon\ge0$, put $B=\lfloor q\epsilon\rfloor$. If $B\le894784857$ and $q<2^{256}$, the same explicit first-failure formula and support-rank answer hold, at every positive width. The exact probability at each real $\delta<447392428/2^{30}$ uses the grid numerator at $e=\lfloor 2^{30}\delta\rfloor$. [Real radii and tolerances](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateToleranceCurve.lean)

The formal argument counts factors of the value-cubic interpolant. A cubic can share at most $3h+26$ sections with the value-quadratic interpolant, by the weighted degree of their resultant. Each irreducible quadratic carries at most 511 labels. Each linear factor above that population lies on an actual affine secant. At most 16 labels can come from scalar-only factors. If the count exceeded $2(e+1)$ at the last step, there would be distinct secants $A,B$ carrying more than 223696214 and 150000000 labels, respectively. Their cores have size at least $t-1$ and $t-2$. A label outside both secants forces their common core to have at least $d-1$ sites. When both cores have size at least $t-1$, all $d$ common roots are forced. Otherwise a label on $B$ needs two fresh sites. If both lie in the opposite core, the folded difference has at least $d+1$ roots and vanishes identically. At most one scalar can cancel the difference identically. The remaining labels on $B$ need distinct sites outside both cores, too few for the asserted population. [Component counting](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateDoubleInterpolation.lean) · [Saturated intersection](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateSaturatedCores.lean) · [Two fresh agreements](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateFreshPairExtension.lean)

The earlier degree-34 interpolation proof establishes the exact numerator through **442128987** errors using a single quadratic interpolant. [Single interpolant](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateQuadraticSafety.lean)

A second Lean proof covers fields of characteristic greater than **1252698792**. At the predecessor it bounds the population by $n$ on every injective domain. A factor carrying too many labels for a proper intersection divides both interpolants. Every common factor carrying more than 263 labels lies on an actual secant. Counting forces two distinct secants with at least 223696215 labels each, whose overlap bounds the total by $n$. It follows that every smooth domain with $q<2^{256}$ and budget at least $n$ is safe through **447392427** errors at every positive width. [Factor divisibility](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateFactorDivisibility.lean) · [Secant extraction](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateCommonPopulation.lean) · [Complete proof](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateCompleteSafety.lean)

## Two interpolants

Suppose $n+1$ distinct genuinely bad labels have been selected, each with a degree-at-most-$d$ folded witness $q_z(X)$ and a nonjoint support of at least $t$ sites. Write $T$ for the scalar indeterminate and $Y$ for the folded value. Use coordinate weights $(1,0,d)$ on $(X,T,Y)$. Here $\Delta=3t-3d-n=2$.

The simple interpolation from the two-head proof gives $Q_1$ of value degree at most two, total $(T,Y)$-degree at most $h=1+\lfloor(n-2d)/2\rfloor=268435458$, and coordinate weight below $t$. The coefficient surplus over the received-line conditions is $h\Delta-(n-2d)=2$.

For $Q_2$ allow value degree at most **three**, total $(T,Y)$-degree at most 16 and coordinate weight below $2t$. The number of coefficients is
$$
\sum_{j=0}^3(17-j)(2t-jd)=50n+357913988 .
$$
The conditions that $Q_2$, its $X$ derivative and its $Y$ derivative vanish identically on each received line require at most $(17+17+16)n=50n$ homogeneous equations. Thus a nonzero $Q_2$ exists. Each agreement is a double coordinate root of $Q_2(X,z,q_z(X))$ by the chain rule. Its degree is less than $2t$, so the specialization is identically zero. Likewise $Q_1(X,z,q_z(X))=0$. [Received-line interpolation](three-rates-two-head-window.md#two-interpolation-polynomials)

## Two large affine families

Work over $\overline F(X)$. The common factors have combined value degree at most two and total $(T,Y)$-degree at most 16. Use primitive integral representatives. The published bounds for their populations apply without changes, since $Q_1$ still has weight below $t$, $t\ge n/3+d$, and $Q_2$ still has total degree at most 16. Their vertical factors carry at most 16 labels. An irreducible common quadratic carries at most 4128, and an irreducible linear-in-value common component carrying more than 184 labels is an actual affine secant. Here an actual secant is a family $q_z=A+zB$ with $A,B$ of degree at most $d$. Each such family carries at most $e+1$ labels. [Population bounds and fresh-site argument](three-rates-two-head-window.md#common-factors-and-the-remaining-intersections)

Let $i$ count distinct common actual secants. For $i\le1$ the residual coprime polynomials have value degrees at most $2-i$ and $3-i$ and scalar degrees at most $h$ and 16. Their value resultant or, for scalar-only residuals, their univariate root bound gives at most $(3-i)h+32$ residual labels. Including all common components gives at most
$$
 i(e+1)+(3-i)h+32+16+2\cdot4128.
$$
This is 805314678 for $i=0$ and 984271648 for $i=1$, both below $n+1$. Thus $i=2$. The first residual has value degree zero and accounts for at most $h$ labels. At most another 16 come from the common vertical factors. There are no further positive-value common factors. Assign labels lying on both secants to either one. Each secant receives at least
$$
 n+1-(e+1)-(h+16)=357913923>e/2+1
$$
labels.

## Equality forces a constant cancellation direction

Write $C_i$ for the full set on which the received row pair equals the two defining polynomials of secant $i$, with $c_i=|C_i|$. Let $L_i$ count its assigned labels. Every such label has a fresh agreement outside $C_i$, since its witness support is nonjoint. A fixed site outside $C_i$ supplies at most one fresh label for head $i$. When $c_i<t$, this yields $(L_i-1)(t-c_i)\le e$. It follows from $L_i>e/2+1$ that $c_i\ge t-1$.

If all selected points lay on the two secants, there would be at most $2(e+1)=894784856<n+1$ of them. Fix an outside point $(z,q_z)$. Its polynomial differs from each folded secant polynomial and agrees with it at at most $d$ coordinates. The two distinct row pairs agree with each other on at most $d$ coordinates, so $|C_1\cap C_2|\le d$. The outside point can have at most
$$
 2d+n-c_1-c_2+|C_1\cap C_2|\le n-2(t-1)+3d=t
$$
agreements. It has at least $t$, so equality holds throughout and $|C_1\cap C_2|=d$.

Let $D(X)$ be the monic vanisher on these $d$ common sites. Both differences of defining row polynomials vanish there and have degree at most $d$. They are $aD,bD$ for field constants $a,b$, with $(a,b)\ne(0,0)$. At a site belonging only to the other head's core, a fresh label for the first head must satisfy $a+bz=0$. Thus all such sites together contribute at most one distinct fresh label to that head. The number of sites outside both cores is at most $n-2(t-1)+d=89478487$, giving $L_i\le89478488$. This contradicts $L_i\ge357913923$ and closes the step. Equivalently, a fresh agreement on the opposite core gives a folded difference of degree at most $d$ with $d+1$ roots. Two distinct such labels would make both row differences zero. [Lean overlap lemma](../../../ArkLib/Research/ProximityGap/Frontier/QuarterRateApolarBracket.lean)

No multiplicative-subgroup assumption enters the lower bound.

At the next step $\Delta=-1$, so the positive surplus for $Q_1$ no longer follows. The unrestricted predecessor at 480946858 errors remains open. The known three-head classification concerns heads on 32 prescribed quotient fibers. [Restricted sharpness](quarter-three-heads-32-fibers.md)

At the first unresolved step, 447392428 errors, failure is equivalent in the written section argument to a split degree-268435454 pencil on the named subgroup. The conditional witness has two more labels than the field budget. [Successor reduction and its remaining algebraic question](quarter-successor-split-pencil.md)
