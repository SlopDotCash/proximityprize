# A ramified elliptic-product cover for the saturated quarter-rate configuration

Work geometrically in characteristic $p>2$ at the named quarter-rate seam. Write $D=(X^n-1)/K_4$ for the squarefree locator of the $4d=n-4$ double sites. The four signed triangle minors, regarded as binary forms of degree $2d$, sum to zero. Name them $A,B,C,-(A+B+C)$. Each root of $D$ is a simple root of exactly two minors. Thus $ABC(A+B+C)=cD^2$ for a nonzero constant $c$. The three independent coordinates of the signed-minor map generate the full rational function field on the source under the four-head overrun hypothesis. [Birationality](quarter-saturated-birational.md) · [Coincidence and direction data](quarter-three-slope-reconstruction.md)

Take the smooth hyperelliptic curve $C_0$ given by $W^2=\sqrt c\,D$. Its genus is $2d-1$. Then $[W:A:B:C]$ maps $C_0$ birationally onto an image curve on the quartic surface
\[
 W^4=ABC(A+B+C).
\]
Indeed the minor ratios recover $X$, after which the normalized $W$ coordinate generates the quadratic extension. This is Vinberg's quartic model of the resolution of the double plane on the six lines of a complete quadrangle. Van Geemen and Top describe the surface's degree-four cover by a product of elliptic curves. The formulas below directly verify the pullback in the prime characteristic under consideration. [Van Geemen and Top, §5](https://pure.rug.nl/ws/files/147436786/2006BullLondonMathSocvGeemen.pdf) · [Double-plane model, §2.1](https://doi.org/10.2140/gt.2017.21.1179)

## The two elliptic maps

Put $t=(B-C)/(B+C)$, $y=(B+C+2A)/(B+C)$ and pass to the smooth curve $C_1$ obtained by adjoining $s$ with
\[
 s^4=1-t^2=\frac{4BC}{(B+C)^2}.
\]
Define $u=2W/(s(B+C))$. Then $u^4=y^2-1$. This yields two maps to the smooth projective curves
\[
 E:\ s^4=1-t^2,\qquad E':\ u^4=y^2-1.
\]
Each quartic double cover of the $s$ or $u$ line has four distinct branch points, hence has genus one. The order-four automorphism multiplying that coordinate by $i$ and fixing the other has a fixed point and gives $j=1728$. We choose origins at fixed points. The constants and signs in the displayed formulas are verified directly. [Lean identities](../../../ArkLib/Research/ProximityGap/Frontier/QuarterQuarticPrym.lean)

Let $e$ be the common edge locator of $B$ and $C$, of degree $h$. The opposite edge has the same degree. Set $m=d-h$, the degree of the corresponding side-direction map. Write $B=eP,C=eQ$ with $P,Q$ coprime forms of degree $L=2d-h=d+m$. Their roots are the four remaining edge strata, which we call the cross sites. They are disjoint and number $2L$. The square class of $s^4$ on the original rational line is $PQ$. Neither $PQ$ nor $PQ/D$ is a square there, since the cross sites and their complementary two strata are both nonempty. An element of the rational line becomes a square after adjoining $\sqrt D$ only if it or its quotient by $D$ was already a square. Thus $s^4$ is nonsquare in the field of $C_0$. Kummer theory gives a connected cyclic degree-four extension $C_1/C_0$.

The pair of projections gives a birational map of $C_1$ onto a curve in $E\times E'$. Indeed $t,y$ recover the minor ratios, hence $X$. The product $su$ recovers the remaining $W$ coordinate, and $s$ generates the last extension. Each projection has degree $2L$. For the first, $t=(P-Q)/(P+Q)$ has degree $L$ on the rational line, the map $C_1$ to that line has degree eight, and $t$ has degree four on $E$. For the second, $y$ is the analogous ratio of the opposite pair of minors, whose common factor has the same degree $h$.

## The precise ramification and its consequence

At every cross site the function $s^4$ has order one on the rational line and order two on $C_0$. Its inertia on $C_1/C_0$ is exactly two. A zero of $P+Q$ on the rational line gives a pole of even order. If it lies over a root of $D$, its order on $C_0$ is divisible by four. Away from the roots of $D$, such a zero gives inertia two at both points of $C_0$ exactly when its multiplicity in $P+Q$ is odd. This counts the point at infinity as well, using homogeneous forms. All other places are unramified.

Let $r$ count these distinct odd-order zeros of $P+Q$ outside the roots of $D$. Riemann–Hurwitz gives
\[
 g(C_1)=10d+2m+2r-7.
\]
One can bound $r\le2m$. Up to sign $B+C$ is the wedge of the two opposite head-difference vectors, by expanding the two triangle determinants along their common side. In the split coordinates for the direction involution the vectors have the forms $e(q,p)$ and $e'(q,-p)$ up to constants, with $e'$ the opposite edge locator. Hence $P+Q$ is a nonzero scalar multiple of $e'pq$ for two coprime binary forms of degree $m$. [Opposite side identity](quarter-saturated-opposite-directions.md)

For the explicit length-16 domain, $d=3$ and each $m=1$. The zero and pole of each of the three displayed fractional linear maps are outside the twelve double sites, so $r=2$ for every opposite pair. Each corresponding $C_1$ has genus 29 and maps with degree eight to each elliptic factor. [The sixteen-site domain and maps](quarter-three-slope-reconstruction.md#an-actual-length-16-witness-on-a-selected-injective-domain)

The generator of the cyclic group acts by $s\mapsto is$, $u\mapsto-i u$ and fixes $t,y$. Its square acts by inversion on both elliptic curves. Consequently the two elliptic maps give an abelian quotient, up to isogeny, of the Prym for $C_1\to C_1/\langle s\mapsto-s\rangle$. Both factors occur: the image curve generates $E\times E'$ up to translation because it is birational to $C_1$ of genus greater than one, whereas a proper positive-dimensional abelian subvariety has genus one.

For the production length, this pullback therefore ramifies at **at least $2(d+m)$** specified marked places of $C_0$. The elliptic factors in this construction occur on the ramified covering curve. An obstruction for the Jacobian of the four-hole curve alone would require an additional argument. The existence of the original smooth-domain four-head overrun remains open.
