# A constant quarter-rate list beyond Johnson

Let \(n\ge1\), let the evaluation points be distinct, and let the characteristic of the coefficient field be zero or a prime \(p>\max(1000000,1000n)\). For every positive interleaving width and every received word, **at most 60,000,015** polynomial words of message degree at most \(n/4\) agree with the received word on at least **\(499999n/1000000\)** sites. The agreement fraction is \(10^{-6}\) below the quarter-rate Johnson fraction \(1/2\). The proof is written mathematics with a finite arithmetic certificate. [Exact verifier](../../../scripts/probes/probe_quarter_list_uniform_length.py) · [Orbit functions and heights](quarter-list-orbit-units.md)

## The normalized interpolation board

Put \(R=1/4,\ s=499999/1000000,\ L=30000000,\ r=1000000,\ r_0=8\). Scalarization into \(k(T)\) preserves word degrees, distinctness and agreements at every width. Extend the resulting coefficient field to its algebraic closure \(k\). Give \(X,Y,V\) weights \(1/n,R,R\). For derivative cap \(h\), use the source and local rank
\[
 S(w,h)=\sum_{j\ge0,\,0\le k\le h}(w-R(j+k))_+,\qquad
 C(r,h)=(h+1)r(r+1)/2-
 \sum_{j=0}^{r-1}(2j+1-r)_+(j+h+1-r)_+.
\]
At cutoff \(P=8s\) and cap two, \(S(P,2)>C(8,2)\), so a nonzero primary equation contains all the word jets. It has total degree at most \(b_0=\lfloor P/R\rfloor=15\) over \(k(X)\) in \(Y,V\). Assign every word to an irreducible factor of that equation. Its factors independent of \(V\) account for at most \(b_0\) words, and it has at most two factors depending on \(V\). It suffices to preclude any one of the latter carrying a finite group of \(L\) words. [Construction and exact lattice rounding](half-list-uniform-length.md#a-source-bound-uniform-in-the-length)

For a primitive factor \(g\) write \(v=\deg_V g\), \(D=\operatorname{wt}g\). Define \(o_x\) as its order in \(u\) under the substitution \((X,Y,V)=(x+u,y_x+uz,z+uz_1)\), where \(z,z_1\) are independent. Let \(\mathbb E\) denote the average over the \(n\) grid sites. Every such group satisfies \(\mathbb E o\ge Z_v(D,h)\), where
\[
 Z_v(D,h)=
 \frac{S(rs,h)-S(rs-D,h-v)-C(r,h)+C(r,h-v)}
 {C(r,h-v)-C(r-1,h-v)} .
\]
Indeed failure produces a secondary equation without the factor, containing all \(L\) jets, whereas the two generic plane equations have at most \(15\lfloor4rs\rfloor=29999940<L\) isolated common jets. This comparison uses the whole group, including any exceptional words omitted when bounding the mean order. The function \(Z_v(D,h)\) is concave in \(D\). [Secondary quotient and degree bound](half-list-uniform-length.md#capturing-a-large-group)

Choose fractional agreements of mass exactly \(sn\) supported on true hits of each word. After omitting at most \(b_0^2\) singular or exceptional jets, their average occupancy \(p_x\) has mean \(s\) and variance at most
\[
 \sigma^2=R-s^2+(s-R)/(L-b_0^2).
\]
The regular derivative bound gives \(\mathbb E o\le1+(D-R)/s+(4D+v)\sigma/(2s)\). For \(v=2\) this lies strictly below \(Z_2(D,h)\) for one cap \(h\) throughout \([2R,P]\). The order margin exceeds \(0.45\). The factor \(g=V\) is excluded by the zero-derivative word bound, or simply by distinctness of constants when the characteristic exceeds \(n\). [Occupancy and regular derivatives](low-rate-uniform-lists.md#changing-the-normalized-weights)

For \(v=1\) put \(g=A+BV,\ e=D-R,\ a=\deg_Y B,\ b=\lfloor4D\rfloor\). Then \(a\le b-1\). On each interval \(bR\le D\le(b+1)R\), the normalized coefficient intersection bound gives
\[
 2j\,\mathbb E o\ \le\ j(j+1)+1+aD+be-abR\quad (j\ge2).
\]
For \(b\le5\) also use the coefficient and content bounds of the low-rate uniform theorem. The verifier chooses nonnegative rational combinations of these inequalities and checks the intercept on every integer order from zero through \(b+1\). [Full coefficient formulas](low-rate-uniform-lists.md#changing-the-normalized-weights)

When \(a=3,\ b\le5\) and \(B\) is squarefree over \(k(X)\), its cubic discriminant has \(X\)-degree at most \(n(4e-6R)\) and local order at least \(2o_x-3\). Thus \(2\mathbb E o\le3+4e-6R\). If \(B\) is a repeated cubic, it factors into primitive linear factors and vertical content, whose normalized degree is at most \(e-3R\le1/2\). At a radial site the lowest nonzero homogeneous term of \(B\) is divisible by \(X-x\), forcing vertical content there. More than half the sites are radial. In fact the proportion of nonradial sites is at most
\[
 (b_0+2)\big[1-s^2/(R+(2s-R)/L)\big].
\]
This follows by counting ordered distinct word pairs in the at most \(b_0+1\) slope classes at every nonradial site. Weighted memberships in \([0,1]\) have square at most themselves, so the identical diagonal correction \(2snL\) also works with fractional agreements. This excludes the repeated cubic in these intervals. [Radial sites and the cubic discriminant](quarter-first-rational-observable.md#slopes-and-orders-below-the-exceptional-weight-interval)

Use both endpoints with a common cap and upper bound in each of the 120 pairs \((a,b)\), \(1\le b\le15,\ 0\le a<b\). For \((a,b)=(4,5)\) increase the left endpoint to \(5R+1/1000\). Every lower order bound exceeds the chosen upper bound by more than \(0.0008\) at both endpoints, hence also throughout each interval by concavity. The remaining case is
\[
    a=4,\quad 5R\le D\le5R+1/1000,\quad \ell=D-5R .
\]

## The quartic with two small orbit functions

Write \(z=Z_1(D,\lfloor r/3\rfloor)\) and \(I_*=4D+5e-20R\), the normalized plane intersection bound. The *fraction* of sites with \(o_x\ne3\) is bounded by \(T=I_*+10-5z\), since \({\bf1}_{o\ne3}\le(o^2-o-1)_++10-5o\). The coefficient bounds give \(o\le6\). The absolute degree cap in \(Y\) on \(A\) is five. For the binary quartic \(B\), each order-three site forces its cubic invariant \(J\) to vanish twice, and \(\deg_X J\le n(3e-6R)\). The verifier checks \(2(1-T)>3e-6R\). Hence \(J=0\). A quartic with a repeated root and \(J=0\) has a triple or quadruple root and splits into linear factors over \(k(X)\). Its vertical content has degree at most \(\ell n\). Off the content a hit at an order-three site gives at least three zeros of \(B(X,f)\) counted with multiplicity. The bound \(3(s-T-\ell)>e\) excludes this possibility. [Quartic invariants and repeated roots](quarter-list-harmonic-involution.md#the-two-invariants-on-the-grid)

The remaining quartic is squarefree and harmonic. In the notation of the harmonic involution proof its projective involution \(\phi\) is defined over \(k(X)\). There are at least \((1-b_*)n\) good physical points with a triple received root and a distinct fourth root, where \(b_*=2T+2\ell\). Indeed the quadratic invariant has degree at most \(n(4R+2\ell)=n(1+2\ell)\), with order at least one at every order-three site and at least two if the cubic Taylor coefficient also vanishes. For each polynomial section apart from the possible pole of \(\phi\), the reduced numerator and denominator of \(\phi(f)\) have degrees at most \((R+u)n,un\), respectively, where \(u=\ell+2R-s+b_*\). The image hits at least \((1-b_*-(2R+\ell))n\) good points. The verifier checks that three times this fraction exceeds \(D+6u\), so each image is a rational solution. Since \(L-1>11\), the generic rational involution commutes with the differential equation. Its fixed points, infinity and \(\phi(\infty)\) are horizontal. Every finite pole of an image lies above a zero of the leading ordinate coefficient of \(B\). The characteristic bound permits the local pole-order argument. These comparisons are lower bounds by concave functions of \(D\), so they hold by checking both exceptional endpoints. [Image denominator, differential identity and fixed sections](quarter-list-harmonic-involution.md#the-involution-sends-each-polynomial-section-to-a-rational-section)

Work over the orbit-label field \(F/k(X)\), of degree \(m\le2\), with heights \(\mathrm h\) divided by \(m\). Put \(h=Y-\phi(\infty)\) and write \(\phi(h)=q/h\) in this translated coordinate. The two monic quadratic orbit factors have the form \(h^2-ah+q,\ h^2-bh+q\), where \(ab=4q\). The degree-two quotient coordinate
\[
 U=\frac{h^2-ah+q}{h^2-bh+q}
\]
sends their two orbits to zero and infinity. Its branch sections are \(+\sqrt W,-\sqrt W\), with \(W=a/b\). Indeed
\[
 U^2-a/b=(1-a/b)\frac{(h^2-q)^2}{(h^2-bh+q)^2}.
\]
Both are horizontal because their lifts, the two fixed sections, are horizontal. At most two polynomial words have a given image \(U_f\).

Let \(E\) contain infinity, the finite exceptions of the orbit-unit lemma, and every grid site that fails its clean conditions. The same degree accounting in that lemma allows \(|E|\le1+n(7T+12\ell)\). The joint bound must be applied at a common weight. Convexity in \(D\) and the two endpoints give \(|E|<1+0.0006n\). At every physical site outside \(E\) the function \(W\) has simple zeros or poles over that site, so \(\mathrm h(W)\ge(n-|E|)/2\). For every surviving section \(U_f\), both \(U_f\) and \(1-U_f\) are units outside \(E\). The height estimate on the orbit-label field gives
\[
 \mathrm h(U_f)\le H=|E|,\qquad
 \mathrm h(U_f')\le2H+|E|+2 .
\]
The elementary preliminary bounds \(\mathrm h(W),\mathrm h(U_f)<20n\) ensure separability when needed. For instance the joint projective height of the coefficients of the monic generic quartic is at most \(en\). By multiplicativity of the Gauss norm at each place, the monic quadratic factors have coefficient heights at most \(en\) in the normalized convention. Evaluation on \(f\) costs at most \(2Rn\) more per factor. Also \(\mathrm h(\phi(\infty))\le(2R+\ell)n\) by its expression in Hessian coefficients. Taking the ratio of the two translated root sums costs at most \(2en+2(2R+\ell)n\). [Orbit reduction, exceptional fibers and the height estimates](quarter-list-orbit-units.md)

## The Riccati equation on the quotient

Let \(\delta=\partial_X-(A/B)\partial_Y\) with \(\partial_X X=1\). The involution commutes with \(\delta\), so its fixed subfield \(F(U)\) is stable. Its rational differential equation has the form
\[
 \delta U=F_0(U),\qquad
 F_0(Z)=c_{-1}/Z+c_0+c_1 Z+c_2 Z^2+c_3 Z^3,\quad c_j\in F.
\]
To justify the pole orders, at a finite ordinate away from the two marked orbits, the upstairs vector field preserves regular functions in a regular coordinate, including at its two fixed points. Its descent has no pole there. The same holds in the infinity chart upstairs since \(\deg_Y A\le5,\deg_Y B=4\). Above \(U=0\) and \(U=\infty\) the quotient is unramified and the upstairs vector field has at most a simple pole at each root of \(B\). Thus \(F_0(Z)\) has at most a simple pole at zero and \(\delta(1/Z)=-F_0(Z)/Z^2\) has at most a simple pole in \(1/Z\) at infinity. These are precisely the stated exponent bounds.

Choose five distinct images \(u_i=U_{f_i}\), all finite and nonzero. The at most two preimages of any image, and the stock \(L\), guarantee five even after discarding the finitely many excluded sections. Interpolate \(ZF_0(Z)\) from its values \(u_i u_i'\). In a Lagrange summand, each coefficient of \(\prod_{j\ne i}(Z-u_j)\) has height at most \(4H\) by its joint pole divisor. The reciprocal of \(\prod_{j\ne i}(u_i-u_j)\) has height at most \(8H\). Including \(u_i u_i'\) gives \(15H+|E|+2\) per summand, so \(\mathrm h(c_j)\le75H+5|E|+10\).

In a separable extension write \(\alpha=\sqrt W\). Horizontality at \(\alpha\) and \(-\alpha\) gives \(F_0(\alpha)+F_0(-\alpha)=0\), hence \(c_0+c_2W=0\). If \(c_2\ne0\) then \(\mathrm h(W)\le150H+10|E|+20\). Otherwise \(c_0=0\), and each \(Z_i=u_i^2\) and \(W\) solve the same Riccati equation
\[
                 Z'=2(c_{-1}+c_1 Z+c_3 Z^2).
\]
Choose three distinct \(Z_i\) among the five squares. If \(W\) equals one of these then \(\mathrm h(W)\le2H\). Otherwise the cross ratio
\[
  \lambda=\frac{(W-Z_1)(Z_2-Z_3)}{(W-Z_3)(Z_2-Z_1)}
\]
has derivative zero. Indeed the logarithmic derivative of each nonzero difference between two solutions \(D_1,D_2\) equals \(2(c_1+c_3(D_1+D_2))\), and all four terms cancel. The normalized preliminary heights give the absolute degree of this cross ratio at most \(2m(\mathrm h(W)+\sum_i\mathrm h(Z_i))<560n<p\) in positive characteristic. On the smooth curve of \(F\) a nonconstant rational function with derivative zero has degree at least \(p\). Thus \(\lambda\) is constant, as also follows directly in characteristic zero. Solving for \(W\) now gives \(\mathrm h(W)\le20H\). Indeed the numerator \(Z_1(Z_2-Z_3)-\lambda Z_3(Z_2-Z_1)\) has height at most \(12H\) and the denominator \((Z_2-Z_3)-\lambda(Z_2-Z_1)\) has height at most \(8H\); they cannot both vanish for three distinct \(Z_i\) and a nonzero cross ratio.

For \(n\ge1000\), the bounds \(H=|E|<1+0.0006n\) and \(\mathrm h(W)\ge(n-|E|)/2\) contradict both upper bounds, as the verifier checks. This excludes the last large group.

For \(1\le n<1000\), the required number \(t=\lceil sn\rceil\) is at least \(n/2\). If \(t=n\), evaluations at all sites determine the word. Otherwise choose exactly \(t\) true hits per word, subtract the constant vector \(t/n\) from their indicator vectors, and scale to unit norm. Pairwise overlaps are at most \(\lfloor n/4\rfloor\), so all off-diagonal Gram entries are nonpositive. For \(M\) words the squared off-diagonal entries are bounded by their negatives, and positive semidefiniteness gives \(\operatorname{tr}(G^2)\le2M\). The rank bound \(M^2=(\operatorname{tr}G)^2\le n\operatorname{tr}(G^2)\) yields \(M\le2n\). This completes the all-length result. Lean checks the polynomial identity for the branch values and the vanishing derivative of the cross ratio for any four Riccati solutions over a field with a derivation. [Formal identities](../../../ArkLib/Research/ProximityGap/Frontier/QuarticHarmonicInvariants.lean)
