# Half-rate MCA safety through 282,513,456 errors at the second prime

Let $h=2^{28}$, $n=4h$, $d=2h-1$ and $t=791228368$. On any injective length-$n$ evaluation domain over a finite field of characteristic greater than 468, including both named primes, every received pair has at most $2n$ MCA-bad scalars at $e=n-t=282513456$ errors. The second prime's first bad count is therefore at least **282,513,457**. The result holds at every positive interleaving width. Its proof uses unrestricted value degrees for the auxiliary interpolation and an exact count of the multiples of a putative irreducible factor. The weight and scalar total degree bounds are enforced simultaneously. [Unrestricted jets on a cubic](second-prime-unrestricted-jets.md) · [Earlier half-rate bound and site jets](half-rate-successor-multiplicity.md)

Work over the algebraic closure $k$ of the base field. Each chosen bad scalar $z$ provides one polynomial $q_z(X)$ of degree at most $d$ agreeing with the received line $L_x(z)$ on at least $t$ sites. The chosen witness precludes a joint explanation. Put $a=e-h=14078000$, and write $m=58$. Use weights $1,0,d$ on $X,Z,Y$. The multiplicity-three interpolation with total $(Z,Y)$ degree at most $m$, value degree at most four and weight strictly below $3t$ has dimension at least

\[
 (m+1)(h+10-15a)-14h+30a-30=42906080.
\]

Take a nonzero interpolant. Its substitution at each chosen section has degree below $3t$ and at least $t$ roots of multiplicity three. Divide out any factors $Z-z$ before specialization: all the translated jet equations are polynomial identities and remain valid. No purely vertical factor can now contain a chosen point over $k(X)$. It suffices to show that a positive-value-degree irreducible factor of degree $b$ carries at most $2hb$ labels, since their value degrees sum to at most four. [Mixed Hasse interpolation](../../../ArkLib/Research/ProximityGap/Frontier/HalfSuccessorJetInterpolation.lean)

## The Hessian and the local jet cost

Suppose an irreducible $F$ of value degree $2\le b\le4$ were to carry more than $2hb$ labels. Take its primitive representative in $k[X,Z,Y]$ and let $W$ be its weight, so $bd\le W\le3t-1$. For each evaluation site $x$ let $i_x$ be the order of $F$ in $(X-x,Y-L_x(Z))$ over $k(Z)$. Since $F$ has no coordinate fiber as a component, $0\le i_x\le b$. The reverse Hessian gives

\[
 \sum_x i_x(3i_x-2)\le (6b-2)W-3b^2d=:H_b(W).
\]

Indeed its affine formula is $F_{ZZ}F_Y^2-2F_{ZY}F_ZF_Y+F_{YY}F_Z^2$. Translation by the received affine function commutes with this expression. At a positive-order site the Hessian has order at least $3i_x-2$. The value resultant bounds the resulting proper local intersections, including sites where the leading coefficient drops. If the Hessian contains $F$, the separable derivative-zero argument instead places $F$ on at most $b$ geometric lines, each with at most one chosen point. Its height test is valid since $b(2m+1)<p$. [Resultant degree, local order and geometric-line case](second-prime-quartic-intrinsic.md)

Fix $\mu=1712$ and $s=536797744$. In the translated $(X,Y)$ jet algebra of total order below $\mu$, the image of multiplication by $F$ has codimension $w_x=\mu i_x-\binom{i_x}{2}$. Its rank follows from injectivity of multiplication by the lowest nonzero homogeneous part before truncation. For an integer $0\le i\le b$ one has

\[
 i(3i-2)\ge(6b-5)i-3b(b-1),\qquad
 \mu i-\binom i2\le(\mu-b+1)i+\binom b2.
\]

Both follow from $(b-i)(b-i-1)\ge0$. Consequently the sum of the local codimensions is at most the affine function

\[
 V_b(W)=(\mu-b+1)\frac{H_b(W)+3b(b-1)n}{6b-5}+n\binom b2.
\]

## Counting the auxiliary polynomials and their multiples

Set $U=\mu t$, $J=\lfloor(U-1)/d\rfloor=2523$, and let

\[
 C_r(v)=\sum_{j=0}^{r}(r-j+1)(v-jd)_+.
\]

There are exactly $C_s(U)$ monomials of weight below $U$ and total $(Z,Y)$ degree at most $s$. For an auxiliary polynomial $P$ on this support impose membership in the image of multiplication by $F$ on every received jet. To impose it as a polynomial identity in $Z$, select independent monomial multiples of the jet of $F$ spanning its image over $k(Z)$. Their entries have degree at most $m$ in $Z$. Give each column an independent multiplier of scalar degree at most $s-m$. On a site where the jet algebra has dimension $A=\binom{\mu+1}{2}$ and the image has codimension $w_x$, the equality of the two polynomial jet vectors has net cost at most $(s+1-m)w_x+mA$ conditions. The multipliers are unique when $P$ is fixed by independence over $k(Z)$. Thus the space of admissible $P$ has dimension at least $C_s(U)-(s+1-m)V_b(W)-mnA$. The identities survive every scalar specialization. [Polynomial-multiplier jet argument](second-prime-intrinsic-cubic.md)

If $F$ divides $P$ over $k(X)[Z,Y]$, Gauss's lemma gives $P=FQ$ in $k[X,Z,Y]$. The total degree and weight of a nonzero product are additive, so $Q$ has total degree at most $s-b$ and weight below $U-W$. This bounds the space of multiples by $C_{s-b}(U-W)$. Hence a solution outside the multiple subspace exists if

\[
 C_s(U)-C_{s-b}(U-W)-(s+1-m)V_b(W)-mnA>0. \tag{1}
\]

The left hand side is concave in $W$: the capacity is a positive sum of positive parts of affine functions and is subtracted, while the remaining dependence on $W$ is affine. It suffices to check the two endpoints $bd$ and $3t-1$ for each value degree. For reproducibility the integer parts of the six lower bounds are

| $b$ | $W=bd$ | $W=3t-1$ |
| --- | ---: | ---: |
| 2 | 44475670712101201886 | 97565269241703132580 |
| 3 | 17958281884818634333 | 188044412403737204942 |
| 4 | 2449811335392357 | 65621072574830083068 |

Lean verifies the nonzero quartic interpolant on the original words, the capacity inequality for every admissible integer weight, and the six endpoint and resultant-degree calculations. The Hessian dichotomy, the dimension of the scalar polynomial jet space, and the exclusion of factors are proved in this note. [Kernel-checked interpolation and arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/HalfRateUnrestrictedJetBudget.lean)

The exact finite sum is evaluated using the first and second sums of integers; the checker also computes the original sum independently. [Exact rational certificate](../../../scripts/probes/probe_half_rate_unrestricted_jets.py)

Take the resulting $P$ which is coprime to $F$. On any section belonging to $F$, at every agreement site $x$ the jet identity specializes at $z$, and substitution $Y=q_z(X)$ sends the order-$\mu$ ideal into $((X-x)^\mu)$. Since $F(X,z,q_z)=0$, the polynomial $P(X,z,q_z)$ has at least $t$ roots of multiplicity $\mu$ and degree below $\mu t$. It vanishes identically. The nonzero scalar resultant with $F$ therefore vanishes on every selected label on $F$. Its scalar degree is at most $bs+mJ\le2hb$ for all $2\le b\le4$. This contradicts the assumed population.

For a linear factor carrying more than $2h$ labels, the identity-site count of the earlier argument applies with 58 in place of 14. There are at least $t-58n/(2h)$ sites where the factor vanishes identically along the received line. The 59 sections missing the fewest such sites each miss at most $58n/(2h-58)$ of them, so any three coincide with their folds on more than $d$ common sites. All 59 therefore lie on one affine head, and total degree at most 58 forces the factor to equal that head. Its bad-scalar count is at most $e+1<2h$ by the fresh-agreement argument. This proves the required per-factor bounds and the stated $2n$ total. [Fresh-site argument](half-rate-successor-multiplicity.md#counting-the-heads) · [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

## Passing from component populations to the literal bad-event count

One can factor over the original field. After removing the part of the interpolant independent of the value variable, at most 58 scalar labels can be exceptional. This follows from the degree bound in the scalar variable applied to one nonzero coefficient of that part. Every remaining label lies on a positive-value-degree irreducible factor. Repeated factors can be counted with multiplicity because their total value degree is still at most four.

For a nonlinear factor of value degree $b$, the section resultant gives the sharper bound $|G|+5048\le536870912b$. The local charge estimate handles a proper Hessian. In the flat case the scalar chart has at most one embedded scalar label. A linear factor carries at most 282,513,457 labels by the secant extraction and occupancy bound. Thus a factor of any value degree $1\le b\le4$ carries at most $536869650b$ labels. Including the exceptions gives at most $58+4\cdot536869650=2147478658$ labels for each received pair. The second prime permits 2,147,483,648 bad labels at the target security level. [Nonlinear population theorem](../../../ArkLib/Research/ProximityGap/Frontier/HalfRateIntrinsicPopulation.lean) · [Linear population theorem](../../../ArkLib/Research/ProximityGap/Frontier/HalfRateLinearPopulation.lean) · [Family count and operational floor](../../../ArkLib/Research/ProximityGap/Frontier/HalfRatePopulationCover.lean)
