# Second-prime MCA safety from shared factor degrees

At length $n=2^{30}$ over the second named prime, every injective evaluation domain is MCA-safe through **313,234,000 errors at rate 1/2** and **534,325,000 errors at rate 1/4**, at every positive interleaving width. These increase the previous safety endpoints by 19,000 and 30,000 errors. The argument bounds the number of bad scalars at width two by the following integers. The reduction from a bound on every received pair to arbitrary positive width is the line-to-affine MCA stability theorem. [Previous half-rate argument](half-blowup-gauss-window.md) · [Previous quarter-rate argument](quarter-blowup-gauss-window.md) · [MCA stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

| Rate | Last safe error count proved here | Bad-scalar cap | Slack below $2^{31}$ |
|---|---:|---:|---:|
| 1/2 | 313,234,000 | 2,145,566,228 | 1,917,420 |
| 1/4 | 534,325,000 | 2,146,821,341 | 662,307 |

## Surfaces and head extraction

Write $t=n-e$ and $d=k-1$. Select one witnessing polynomial $q_z$ for each bad scalar $z$. The primary and companion surfaces of orders $r_i$, ordinate degrees at most $v_i$, and total $(Z,Y)$-degrees at most $s_i$ vanish on these sections. Their mixed jets give order at least $r_i$ on every received line. The four rank surpluses are positive. [Construction and exact ranks](../../../ArkLib/Research/ProximityGap/Frontier/SharedFactorDegrees.lean)

| Rate | Surface | $(r_i,v_i,s_i)$ | Columns minus constraints |
|---|---|---|---:|
| 1/2 | Primary | $(89,126,295664)$ | 4,238,610 |
| 1/2 | Companion | $(174,246,14868)$ | 1,662,163,854 |
| 1/4 | Primary | $(53,106,130044)$ | 108,222,714 |
| 1/4 | Companion | $(104,208,7551)$ | 14,248,080,392 |

As in the previous allocation, factor the surfaces over the algebraic closure of the constant field with primitive polynomial representatives. Give priority to sections on a polynomial affine head of the primary and assign each such section to one head. A head with more than $s_1$ assigned labels divides both surfaces by substitution since $s_2<s_1$. Let $j$ be the number of rich heads. Their combined degree consumption is at least $j$ in both ordinate and plane degree, and at least $jd$ in coordinate/ordinate weight. The remaining sections after the affine-head assignment lie on none of the rich heads. Value-independent primary factors cost at most $s_1$ scalars. Each small affine head costs at most $s_1$ by its definition. [Primitive factor and head extraction](quarter-common-factor-degrees.md#one-resultant-and-one-total-degree)

Take $\ell=1+\lfloor e/s_1\rfloor$ and $C=t-\ell$. The rich-head core inequality $(L-1)(t-c)\le e$ for a head of population $L$ and core size $c<t$ gives $c\ge C$. We have $3C>n+2d$. For $j<3$ use the separate rich-head cost $J_j=j(e+1)$. For $j\ge3$ the heads are collinear. Put
\[
 U_j=\max_{1\le a<j}\left\lceil\frac{2ajC-j(j-1)d}{a(a+1)}\right\rceil,\qquad
 V_j=\max\left(U_j,\left\lceil\frac{jC^2}{C+(j-1)d}\right\rceil\right).
\]
Charge $J_j=\min(j(e+1),\max(0,jn-(j-1)V_j))$. These are the discrete and Cauchy core-union bounds for collinear heads. [Head populations and transverse tangents](quarter-transverse-tangents.md)

## Assigning common and noncommon sections

After the affine-head and value-independent assignments, assign any remaining section lying on a common nonlinear factor to one such factor. Call a common nonlinear factor *active* if it receives at least one section in this assignment. Next assign sections on common nonaffine linear factors. Every remaining section then lies on a noncommon primary factor and lies on none of the active common nonlinear factors or rich heads. This priority makes it possible to divide out both the rich heads and the active nonlinear factors before bounding the resultant for these last sections.

For an active nonlinear factor $F_i$, let $m_i=\deg_{Z,Y}F_i$ and $b_i=\deg_Y F_i\ge2$. Set $S=\sum_i m_i$. When at least one factor is active, put
\[
 c=\max_i b_i,\qquad u=v_1-j-c,\qquad D=v_2-j-c,\qquad z=s_2-j-S.
\]
All three residual degrees $u,D,z$ are nonnegative. Remove one copy of each rich head and each active nonlinear factor from the companion. Its residual plane degree is at most $z$ and its ordinate degree is at most $\min(D,z)$. The product of the distinct noncommon primary factors receiving the last sections is coprime to the residual companion as ordinate polynomials and primitive. Its plane degree is at most $s_1-j-S=s_1-s_2+z$ and its ordinate degree at most $u$. We may omit it entirely if no such section exists. The original companion vanishes on each of these sections, and every removed factor is nonzero upon substitution, so its residual also vanishes. Taking the scalar degree of the nonzero ordinate resultant bounds their number by
\[
 (s_1-s_2+z)\min(D,z)+uz.
\]
This argument also applies if the companion has positive scalar degree and ordinate degree zero. [Resultant implication with degree drops](../../../ArkLib/Research/ProximityGap/Frontier/DoubleInterpolationCommonFactor.lean)

The remaining small affine heads collectively cost at most $us_1$. Write $L=1+\lceil4n/(t-d)\rceil$, equal to 21 and 17 in the two windows. Each common nonaffine linear factor of plane degree $m$ carries at most $Lm$ sections. Their total plane degree is at most $z$, as these factors are distinct from all removed ones. If $u=0$, the active nonlinear factors and heads exhaust the primary ordinate degree, so there are no further positive-ordinate factors. If $u=1$, at most one other positive-ordinate factor can occur in the primary. If it is polynomial affine, its residual population is at most $s_1$. Otherwise the value-linear extraction theorem bounds its entire population by $L(s_1-s_2+z)$, whether or not it is common. This accounts for all three classes of remaining positive-ordinate factors in this case. In particular, when the extraction theorem places a set of more than $Lm$ sections on one polynomial affine head, substituting that head gives more than $m$ scalar zeros and forces the irreducible linear factor to equal the head. [Value-linear extraction](../../../ArkLib/Research/ProximityGap/Frontier/GeneralLinearFactorExtraction.lean)

## Common nonlinear population

For each active factor use the blown-up Gauss-graph and tangent bounds with the same companion-cofactor dichotomy as in the prior windows. If all its assigned sections lie on the cofactor obtained after removing all copies of the rich heads and $F_i$, the coprime fallback costs at most $(s_2+v_2-2j)m_i$. Otherwise a section outside that cofactor and the rich heads supplies $W+1\le\sum_{x\in T}i_x$ for its $t$ agreements. This gives the previously proved bound on the pole height with the maximal weight $W=\min(r_1t-1-jd,b_it-1)$. Neither alternative requires priority over a noncommon primary factor. The tame-characteristic inequalities $2r_1tv_1<p_2$ and $s_2(s_2-1)<p_2$ hold in both rows. [Cofactor dichotomy and height](half-blowup-gauss-window.md#15-two-case-factor-assignment-and-monotonicity-of-blowuph)

For clarity, the verifier uses the following per-unit-plane-degree prices. For a factor of ordinate degree $b$, the ordinary incidence loss and the pole-height bound are
\[
 R=(2b-1)n,\qquad H=(6b+2)W-3b^2d-\left\lfloor 3(W-t)_+^2/t\right\rfloor-2(W-t)_+.
\]
With $p=\min(j,2)$ the triangle price is $6b-2+\lceil(3-p)(H+R)/(3t-n-2d-p\ell)\rceil$. For at least three rich heads at half rate or four at quarter rate, take the lesser of this and $6b-2+\lceil(H+R)/(t+U_j-n-d)\rceil$. At $j=0$ for half rate, use the Veronese levels $(s,a)=(6,5),(12,10),(24,20)$. At $j\le3$ for quarter rate use $(4,3),(8,6),(16,11),(24,17)$. Each level applies for $m>s(s-1)$. With $h=\binom{s+2}{2}$ and $p'=\min(j,3)$ the additional available price is
\[
 4b-2+2sb+
 \left\lceil\frac{(h-p')(aR+sH)}
 {aht-\binom{a+2}{3}n-s(s+1)(s+2)d/3-ap'\ell}\right\rceil .
\]
For each actual degree range use the cheapest applicable tangent price, raised if necessary to the coprime fallback. [Half-rate tangent prices](half-blowup-gauss-window.md) · [Quarter-rate Veronese prices](quarter-blowup-gauss-window.md#2-veronese-ladder-and-dual-pricing)

For fixed $j,b$, write $\alpha_b$ for this unit price in the last degree range. For each earlier range with upper endpoint $q$ and price $P$, set $\beta_b$ to the maximum of zero and the numbers $\lceil q(P-\alpha_b)/b\rceil$ over those ranges. Thus the population of a factor with actual degrees $b,m$ is at most $\alpha_b m+\beta_b b$ for every $m\ge b$. Set $A=\max_{2\le b\le c}\alpha_b$ and $B=\max_{2\le b\le c}\beta_b$. Summing gives the total active nonlinear cost $AS+B(v_1-j)$.

## Maximizing the residual charge

Start at $J_j+s_1+A(s_2-j)+B(v_1-j)$. If $u=0$ this already bounds all the labels. For $u=1$ add $\max(s_1,L(s_1-s_2))$. This is sufficient because $A\ge L$ and increasing the unused plane degree $z$ decreases the common nonlinear charge by $Az$.

For $u\ge2$ add $us_1$ for the small heads. The remaining charge relative to this starting point is bounded by
\[
 f(z)=(s_1-s_2+z)\min(D,z)+(u+L-A)z.
\]
Every degree case satisfies $A\ge D+u+L$. On $0\le z\le D$ this quadratic has maximum at one of its endpoints. For $z\ge D$ its slope is nonpositive. Thus it suffices to add $\max(0,D(s_1-s_2+D+u+L-A))$. When the active nonlinear set is empty, use the single bound
\[
 J_j+s_1+(s_1-j)(v_2-j)+(v_1-j)(s_2-j+s_1)+L(s_2-j).
\]
It charges the noncommon resultant after removing the rich heads, all small heads and all common nonaffine linear factors. [Lean proofs of both residual bounds](../../../ArkLib/Research/ProximityGap/Frontier/SharedFactorDegrees.lean)

The exact verifier checks the two rank surpluses per rate, all denominators and slope inequalities, all $0\le j\le v_1$ in the empty case and all $2\le c\le v_1-j$ in the nonempty case. The latter gives 7,875 half-rate cases and 5,565 quarter-rate cases. The maxima occur at $(j,c)=(4,120)$ and $(3,101)$ respectively. A uniform bound at the displayed agreement count also holds at every higher agreement count by monotonicity. The full MCA conclusions combine the written geometric results above with exact integer verification. Lean certifies the four interpolants, both shared-degree inequalities, and the population caps with every residual slope test. Its union bound evaluates the floor and ceiling of $j/2$ and $7j/10$ whenever admissible; the independent Python check maximizes over every admissible integer $a$. Both give the same worst-case caps. [Reproduce both maxima](../../../scripts/probes/probe_shared_factor_degrees.py)
