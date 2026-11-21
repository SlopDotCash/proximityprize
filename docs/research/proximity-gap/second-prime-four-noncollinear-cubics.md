# A quarter-rate attack with four noncollinear vector cubics

At the second named prime and length $n=2^{30}$, one quarter-rate received pair has at least **2,214,592,518 distinct MCA-bad scalars at 553,648,129 errors**. This lowers the previous four-head ceiling by 11,983,725 errors. The scalar budget is 2,147,483,648. Lean verifies the mass throughout dimensions 268,435,456 to 520,093,694 and at every positive interleaving width. [Noncollinear quarter-rate theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimePlanarQuartet.lean) · [Finite-field certificate](../../../scripts/probes/probe_second_prime_four_cubics.py)

Write $s=2^{26}$, $k=4s$, $w=g^s$ for the named generator, and $t=X^s$. For an exponent set $A$, write $L_A(t)=\prod_{j\in A}(t-w^j)$. Start with four polynomial pairs of degree at most three. Head zero is the zero pair. Head one is $(L_{0,2,4},0)$. Head two is $(bL_{5,13},(t-w^6)L_{5,13})$ with $b=L_{0,2,4}(w^6)/L_{5,13}(w^6)$. Head three is the cubic in each entry that agrees with head two at exponents 8, 10 and 12 and with head one at exponent 15. In each pair replace the second entry by the sum of its two entries, calling the resulting coordinates $U_i,V_i$.

| Head pair | Equality exponents |
|---|---|
| 0, 1 | 0, 2, 4 |
| 0, 2 | 5, 13 |
| 0, 3 | 14 |
| 1, 2 | 6 |
| 1, 3 | 7, 15 |
| 2, 3 | 8, 10, 12 |

Direct field evaluation gives exactly these twelve double sites. It also checks that every two distinct values have distinct second coordinates, and that any three distinct planar values at a single site are noncollinear. Each quotient fiber has $s$ production coordinates.

Receive the matching double head on each of the twelve pair fibers. The four private fibers have exponents 1, 3, 9, 11. In the first two select $s/4-1$ common roots, and in the other two select $s/4$ each. Their locator $J$ has degree $s-2$. Assign the remaining sites of the four private fibers to heads 0, 1, 2, 3 respectively. Each defining core now includes the common roots, six complete pair fibers, and at least $3s/4$ private sites. The minimum core size is $C=31s/4-2=520093694$.

For parameters $a,b$ give head $i$ the polynomial pair
\[
 (a J U_i(X^s)+ b X J V_i(X^s),\quad J V_i(X^s)).
\]
Both entries have degree less than $k$. The received entries at each site are those of its owner. At every nonroot $x$, a foreign head $i$ whose quotient value differs from its owner $h$ gives the label
\[
 a\frac{U_h(x^s)-U_i(x^s)}{V_i(x^s)-V_h(x^s)}-b x .
\]
The coefficient pairs distinguish different sites by their second coordinate, and distinguish foreign values at a common site by the determinant check. Two different coefficient pairs exclude one proper linear condition on $(a,b)$. Fewer than $p$ such conditions suffice to avoid all collisions simultaneously. Every chosen label agrees on its head's core plus the foreign site. A simultaneous fit to both rows would have to equal the head on every coordinate by polynomial uniqueness on its core, contradicting the second-row mismatch at the foreign site.

The twelve pair fibers give $24s$ labels. The $3s+2$ private sites give $9s+6$ more. The total is $33s+6$, at $n-C-1$ errors. The same attack works at every positive interleaving width by MCA stability. The unrestricted first failing count still needs a matching lower bound.

## Factorization over every smooth coset

Write $b=w^2$, $a=w^{14}=b^{-1}$, $R=t-a$, $S=t+a$, $C=t^2+b$, $D=t^2-a$, $A=RC-bSD$ and $M=bRD-SC$. Use the four planar heads $(0,0)$, $(A,0)$, $(RC,SC)$ and $(RC,bRD)$. The six pair locators in lexicographic edge order are $A,C,R,S,D,M$. In particular
\[
 A=(1-b)(t-1)(t-w^2)(t-w^4),\qquad
 M=-(1-b)(t-w^8)(t-w^{10})(t-w^{12}).
\]
The four oriented triangle determinants in lexicographic order are $ACS$, $bARD$, $RCM$ and $bSDM$. Each splits completely over the sixteenth roots in every field containing an element of that order. Among the sixteen fibers, a second-coordinate projection fails to separate a pair at only one slope for each pair of distinct values having distinct first coordinates. A field with more than 256 elements supplies one common projection.

On a coset of length $64m$ the substitution $t=(X/u)^{4m}$ uses the inverse coset representative $u^{-1}$. Choose $m-1,m-1,m,m$ common roots on the four private fibers. Their locator has degree $4m-2$. The four cores have sizes $31m-1,31m-1,31m-2,31m-2$. Their complements supply $132m+6$ labels at $33m+1$ errors. This applies from dimension $16m$ through $31m-2$. The first failing error count for unrestricted received words at the second prime is still open at quarter rate. [Formal coset theorem](../../../ArkLib/Research/ProximityGap/Frontier/SmoothPlanarQuartetCoset.lean)

## Predecessor obstruction

At $33m$ errors a head needs $31m$ agreements. Suppose all four heads reduce outside $R$ by a common pointwise injective map to planar polynomials of degree at most $d$, with three noncollinear and the fourth distinct. If $C_i$ are their joint cores, the four-head determinant applied to $C_i\setminus R$ gives
\[
 \sum_i |C_i|\le n+3|R|+4d.
\]
The three copies of $|R|$ come from allowing four cores to agree at each exceptional site, while the union away from $R$ has size at most $n-|R|$. When $3|R|+4d+5\le60m$, one core has size at most $31m-2$. A label on that head needs at least two agreements outside the core, and different labels use disjoint such sites. The three other heads each have at most $33m+1$ labels. The four heads together account for at most $\lfloor(231m+8)/2\rfloor$ labels. At the named length this gives 1,937,768,452, short of the second-prime budget by 209,715,196. It covers the constructed family with $d=12m$ and $|R|=4m-2$. [Kernel-checked predecessor cap](../../../ArkLib/Research/ProximityGap/Frontier/FourHeadCommonRootObstruction.lean)

## The antipodal degree-seven extension

A direct extension of the cubic would use opposite edge multiplicities $7,6,1$ on the 32nd roots. In the sign-symmetric version, normalize the singleton pair to $\{1,-1\}$. The opposite size-seven edges have locators $A(t)$ and $A(-t)$, where $A$ is monic with one root from each of seven other antipodal pairs. The two size-six edges have even locators $C(t)$ and $D(t)$. For nonzero constants $u,v$, this construction requires
\[
 A(t)=u(t-1)C(t)-v(t+1)D(t).
\]
At a root of $C$, this forces $(t-1)A(t)=(-t-1)A(-t)$. At a root of $D$ it forces $(t+1)A(t)=(-t+1)A(-t)$. The six disjoint eligible antipodal pairs would have to come from the eight unused pairs. Over $\mathbb F_{65537}$, screening all $\binom{15}{7}2^7=823680$ choices for $A$ gives at most two eligible pairs in total. [Reproducible exact computation](../../../scripts/probes/probe_antipodal_septic_quartet.py)

This rules out the same construction at the second named prime. Each tested equality is a difference of two products of eight root differences in $\mathbb Z[\zeta_{32}]$. Its absolute value at each of the sixteen complex embeddings is at most $2^9$. Hence a nonzero norm has absolute value at most $2^{144}$, below the production prime. An equality there must already hold in $\mathbb Z[\zeta_{32}]$ and survive specialization to the screen field. Other degree-seven configurations remain open.
