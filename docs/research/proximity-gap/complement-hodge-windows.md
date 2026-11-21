# Complementary fibre divisors improve three second-prime MCA bounds

At length $n=2^{30}$, on every injective evaluation domain in the second named prime field, the following error counts are safe at tolerance $2^{-128}$. The integer budget is $2n=2,147,483,648$. The argument works at every positive interleaving width by the MCA stability theorem. The geometric input is the written normalization, ramification and section-incidence argument used in the preceding weighted windows. Lean verifies the moment inequality, both jet dimension counts, the head tests and every degree allocation in the new windows. [Previous geometric estimates](weighted-hodge-windows.md) · [Lean certificates](../../../ArkLib/Research/ProximityGap/Frontier/ComplementHodgeWindows.lean) · [Exact-arithmetic checker](../../../scripts/probes/probe_complement_hodge_windows.py)

| Rate | Safe errors | Upper bound on bad labels | Lower bound on first failing error count | Increase in the previous written floor |
|---|---:|---:|---:|---:|
| $1/2$ | 299,700,000 | 1,630,997,447 | 299,700,001 | 600,000 |
| $1/4$ | 516,200,000 | 2,030,538,477 | 516,200,001 | 1,800,000 |
| $1/8$ | 665,900,000 | 2,107,604,375 | 665,900,001 | 300,000 |

## Intersection estimate for the complementary divisor

Use the normalized surface of an irreducible component of value degree $b\ge2$, total scalar/value degree at most $m$, and coordinate/value weight at most $W$. Fix a coordinate $x$, write $\Phi_x=\sum_i e_iD_i$ for its scheme-theoretic fibre, and put $w=Y-L_x(Z)$ for the prescribed received line. The truncated divisor $A_x=\sum_i\min(e_i,\max(0,\operatorname{ord}_{D_i}w))D_i$ has degree $f_x=A_x\cdot\Phi_Z$ over the scalar line. The established estimate is $-A_x^2\le m f_x$. The divisor $A'_x=\Phi_x-A_x$ has the same self-intersection since $\Phi_x$ intersects every fibre component with multiplicity zero. Its coefficients are the truncations of the orders of $(X-x)/w$, because clipping $e_i-u$ to $[0,e_i]$ gives $e_i$ minus the clipping of $u$. [Fibre classes and truncated orders](hodge-section-variance.md#truncating-the-order-of-the-received-function)

Write $a_b(X,Z)$ for the coefficient of $Y^b$ in the component equation. On the affine scalar chart it has scalar degree at most $m-b$. At a horizontal prime divisor of the normalization with finite scalar coordinate, the coefficients are integral in its valuation ring. If $w$ has a pole then $Y$ has the same pole. In the reversed value equation, $a_b$ is a multiple of $1/Y$ in the valuation ring. Thus $\operatorname{ord}(a_b)\ge-\operatorname{ord}(w)$ there. On the other chart put $Z'=1/Z$, $Y'=Z'Y$. Homogenization gives integral coefficients and leading coefficient $a'_b=(Z')^{m-b}a_b(X,1/Z')$. The received value $Z'L_x(1/Z')$ is integral. By the reversed equation for $Y'$, the pole order of $w$ is at most $\operatorname{ord}(a'_b)+\operatorname{ord}(Z')$. The latter term accounts for the whole line at scalar infinity with its pullback multiplicities. [Local-ring divisibility](../../../ArkLib/Research/ProximityGap/Frontier/ComplementHodgeWindows.lean)

Along a horizontal prime, $X-x$ is a unit. All horizontal zeros of $(X-x)/w$ near $\Phi_x$ are therefore dominated by the pullback of the homogenized leading-coefficient curve plus scalar infinity. Remove the exact factor $(X-x)^a$ from $a_b$ before homogenizing, which preserves horizontal orders and ensures the curve contains no component $\{x\}\times\mathbb P^1$. The resulting base divisor has degree $m-b+1$ in the scalar on the coordinate fibre. The projection formula bounds its intersection with $A'_x$ by $(m-b+1)(b-f_x)$. Applying the same clipping inequality and principal-divisor calculation to $(X-x)/w$ proves

$$0\le -A_x^2=-{A'_x}^2\le\min\bigl(mf_x,(m-b+1)(b-f_x)\bigr).$$

This calculation uses the rational intersection pairing on the normal surface. The horizontal curve is Cartier on the base and its pullback intersects the effective complementary divisor by the projection formula. [Mumford, *The topology of normal singularities of an algebraic surface*](https://www.numdam.org/articles/10.1007/BF02698717/)

## From the intersection bound to a component count

Retain $N$ simple sections after removing at most $B_X=(2b-2)m-b(b-1)+1$ scalar fibres. Write $B_Z=(2b-2)W-b(b-1)d+1$. At an interior fibre $0<f_x<b$ use $\min(f_x,b-f_x)$ in the weighted Hodge inequality for $T_x=A_x-(f_x/b)\Phi_X$. Since $-T_x^2\le m\min(f_x,b-f_x)$, the total normalized squared cost is at most $4bmB_XB_Z$. Each of the at most $mn+B_XB_Z$ exceptional section/site pairs incurs an extra cost of at most $b$, because its original and replacement squared deviations lie in $[0,1]$ and both interior integral degrees are at least one. At $f_x=0,b$ the finite map ensures $A_x=0,\Phi_x$ respectively. All discrepancies there are exceptional and cost $b$ per pair. [Variance and exceptional pairs](hodge-section-variance.md#the-agreement-indicator-on-the-normalized-surface)

Let $\theta$ be the agreement fraction at a site and $g=f_x/b$. Its mean weighted cost is $V=(\theta(1-2g)+g^2)/\min(g,1-g)$ for $0<g<1$, with costs $b\theta$ and $b(1-\theta)$ at the endpoints. For $0<g\le1/2$, one has $V\ge\min(1/2,2\theta)$. For $\theta\ge1/4$ multiply by $g$ and use $(g-1/2)^2\ge0$. For $\theta\le1/4$ the required inequality follows from $\theta(2g-1)^2+(1-4\theta)g^2\ge0$. Complementation exchanges $(\theta,g)$ with $(1-\theta,1-g)$. In particular

$$\frac{39}{40}\theta-\theta^3\le\frac34 V.$$

Indeed the left side is at most $3/8$, $3\theta/2$ and $3(1-\theta)/2$. The first and third inequalities follow from the cubic tangents at $4/7$ and $109/120$, respectively. Sum over the sites and use $\sum\theta\ge t$ together with the three-section determinant bound $N\sum\theta^3\le Nd+(n-d)(m+1)$. Adding back the removed labels proves the cap

$$B_X+\left\lfloor\frac{30b(4m B_XB_Z+mn+B_XB_Z)+40(n-d)(m+1)}{39t-40d}\right\rfloor.$$

## The finite windows

Use the same two-surface and rich-affine-head argument as the previous weighted estimate, with the following multiplicity, value degree and total scalar/value degree triples. The rich-head population cutoff is the maximum of $1+\lfloor e/256\rfloor$ and $1+s v'+v m$, for primary shape $(r,v,s)$ and companion $(r',v',m)$. Outside at most $s$ vertical labels the primary factors cover every selected witness. The maxima in the opening table include those $s$ labels. [Two-surface and degree-allocation argument](weighted-hodge-windows.md#joint-allocation-among-linear-and-nonlinear-factors)

| Rate | Primary | Companion | Column surpluses | Rich-head cutoff |
|---|---|---|---|---:|
| $1/2$ | $(7,10,3647)$ | $(13,18,118)$ | $6,481,247$ and $1,482,753,280$ | 1,170,704 |
| $1/4$ | $(6,12,28435)$ | $(12,24,129)$ | $1,076,366$ and $2,679,620,404$ | 2,016,407 |
| $1/8$ | $(4,12,21302)$ | $(8,24,87)$ | $526,008$ and $2,094,809,084$ | 2,601,172 |

## Sharper ramification at smooth branch points

The same normalized-cover argument improves the global bound from $4B_XB_Z$ to $2B_XB_Z$. Retain the assumptions of the horizontal ramification lemma, including tame covering degree and separable tame projection of each nonhorizontal reduced branch component to the scalar line. The characteristic inequalities there guarantee both. A retained section maps isomorphically onto a parameter line outside the excluded horizontal branch components. The existing inequality on the resolution bounds the local ramification intersection against a section by the local intersection $a$ of this line with the reduced branch curve. [Ramification lemma and intersection conventions](section-incidence-hodge-index.md#four-lemmas)

At a smooth branch point the tame chart improves the bound to $a-1$. Above the strict local chart of a single smooth branch divisor with uniformizer $t_0$, the ramified factor has form $u^e=t_0$ after étale localization. Its source is regular there, and the ramification divisor has coefficient $e-1$ on $u=0$. On the chosen section the order of $t_0$ is $a$, so $a=e\operatorname{ord}(u)$. The latter order is a positive integer and the intersection contribution is $a-\operatorname{ord}(u)\le a-1$. An unramified lift has contribution zero. At a singular branch point use the former bound $a$. Each base point lies on at most one chosen horizontal line and the section meets it in a single point. These arguments also apply in the two affine charts at infinity. [Abhyankar's lemma for a regular divisor](https://stacks.math.columbia.edu/tag/0EYG)

Remove horizontal components to obtain the reduced curve $B'$. Distinct horizontal parameter lines are disjoint, so the deletion has no effect on any retained line. For the normalization projection of $B'$ to the scalar line, the intersection deficiency on a parameter line is the sum of the ramification excesses plus $r_P-1$ at its points, where $r_P$ is the number of geometric branches. Summing over all lines bounds the surplus for any subset of them. Riemann–Hurwitz, including the number of components when the normalization is disconnected, gives total ramification $2p_a(B')-2+2\deg(\pi)-2\sum_P\delta_P$. To cover the one extra unit allowed at each singular point, use $(r_P-1)+1\le2\delta_P$, since $r_P-1\le\delta_P$ and each singular point has $\delta_P\ge1$. Consequently the sum of ramification costs of the retained sections is at most $2p_a(B')-2+2\deg(\pi)\le2B_XB_Z$ by the bidegree genus formula. An empty $B'$ gives zero. [Local integer inequalities and finite bounds](../../../ArkLib/Research/ProximityGap/Frontier/ComplementHodgeWindows.lean)

## Component counts at every agreement above the code degree

For $0\le\theta,g\le1$ the site cost $V$ above satisfies $\theta-\theta^3\le V$ for $b\ge2$, and $\theta-\theta^3\le(77/100)V$ for $b\ge3$. For interior $g$ with $\theta\in[1/4,3/4]$ the earlier half-fibre inequalities give $V\ge1/2$, and $\max(\theta-\theta^3)=2/(3\sqrt3)$. When $\theta\le1/4$, the same inequalities give $V\ge\min(1/2,2\theta)$. For $\theta\ge3/4$ put $u=\sqrt{1-\theta}\le1/2$. For $g\ge1/2$ the square $(1-g-u)^2\ge0$ gives $V\ge2u(1-u)$, and $u(1+u)(2-u^2)\le3/2$. For $g\le1/2$ one still has $V\ge1/2$. At the endpoint $g=1$, the ratio is bounded by $2/b$, and at $g=0$ it is bounded by $1/b$. These calculations give the sharp uniform penalty $4/(3\sqrt3)$ for $b\ge3$, attained in degree four at $g=1/2$ and $\theta=1/\sqrt3$. The formal bound uses the rational upper bound $77/100$. For $b=2$ the endpoint $g=1$, $\theta\to1$, forces penalty one.

With $P_b=77$ if $b\ge3$ and $P_2=100$, the preceding ramification estimate therefore gives every nonlinear component the population cap

$$B_X+\left\lfloor\frac{P_b b(2m B_XB_Z+mn+B_XB_Z)+100(n-d)(m+1)}{100(t-d)}\right\rfloor.$$

This holds for every $t>d$, including agreements below Johnson, whenever the component carries the sections described in the geometric hypothesis. Producing a suitable component uniformly for every received pair remains a separate issue at those agreements. The formal section cap states the finite-moment hypotheses explicitly. [Component cap in Lean](../../../ArkLib/Research/ProximityGap/Frontier/ComplementHodgeWindows.lean)

## Improved named windows with the tame contact estimate

The final written bounds combine the preceding generalizations. They improve the first table by a further 1,900,000, 1,400,000, and 1,500,000 Hamming steps respectively. Counts include the primary scalar-only factor allowance. All component prices, rich-head tests and interpolation surpluses have exact certificates. [Lean arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/ComplementHodgeWindows.lean) · [Independent enumeration](../../../scripts/probes/probe_complement_hodge_windows.py)

| Rate | Safe errors | First failure at least | Maximum bad labels | Primary | Companion | Jet surpluses |
|---|---:|---:|---:|---|---|---|
| $1/2$ | 301,600,000 | 301,600,001 | 2,075,412,585 | $(8,11,1224)$ | $(15,21,152)$ | 11,020,760 and 315,785,248 |
| $1/4$ | 517,600,000 | 517,600,001 | 2,131,667,446 | $(7,13,7818)$ | $(13,26,147)$ | 6,307,126 and 2,350,708,659 |
| $1/8$ | 667,400,000 | 667,400,001 | 2,146,821,649 | $(5,13,431)$ | $(8,24,96)$ | 76,079,389 and 429,878,408 |
