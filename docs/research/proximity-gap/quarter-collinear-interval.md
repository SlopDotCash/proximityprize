# The same split pencil controls 33,554,431 quarter-rate error counts

Let $n=2^{30}$, $k=n/4$, $d=k-1$, and $e_0=447392428$. Work on the specified subgroup in the first designated prime, and let $M(e)$ be the maximum number of genuinely bad scalar labels of a received pair at $e$ errors. Write $j=e-e_0$.

For **all 33,554,431 error counts** from $e_0$ through **480946858**, the predecessor of the known attack,
\[
 M(e)>n+6j\quad\Longleftrightarrow\quad
 \text{there exist three disjoint full fibers of degree }268435454
 \text{ in a polynomial pencil on the subgroup}.
\]
If the pencil exists, $M(e)=n+2+6j$ at **every** count. Otherwise $M(e)\le n+6j$ at every count. The unconditional upper bound at the terminal predecessor is **1275068406**. Existence of the pencil in the named field remains open. At every positive interleaving width, divide the numerator by the field order to obtain the same MCA probability bounds. [Single-step pencil and field question](quarter-successor-split-pencil.md) · [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

Every overrun of the named budget $n$ through **469762048 errors** requires precisely three distinct collinear affine polynomial heads covering all selected labels. Through **472957611 errors** it requires three or four such heads, with every label covered. Through the terminal predecessor the only other possibility is three rich collinear heads and at most 2047 outsiders. The outsider case obeys the stronger bound $M_{\mathrm{family}}\le n-536868843+21j$. The proof uses the written normalized-surface variance estimate. Lean checks the interpolation surplus, all nonlinear populations, the three-core outsider inequality on actual finite sets, the integer bounds and the construction of one received pair from the split polynomials. [Section variance](weighted-hodge-windows.md) · [Interval certificates](../../../ArkLib/Research/ProximityGap/Frontier/QuarterCollinearInterval.lean) · [Parametric witness](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSuccessorSplitPencil.lean)

## A single quartic throughout the bracket

Take $t_*=592794966$, the smallest required agreement count, and a surface of value degree at most four, total scalar/value degree $m=121$ and coordinate/value weight less than $2t_*$. The monomial count is $\sum_{b=0}^4(122-b)(2t_*-bd)=365n+1990$. Vanishing to order two on each received line costs at most $365n$ homogeneous conditions. Choose a solution of minimal total scalar/value degree. Division by a scalar-only factor $Z-z$ preserves all three jet equations, so no selected label is lost to such a factor. Every witness lies on a positive-value irreducible factor by the double-root count. [Double interpolation and removal of vertical factors](quarter-successor-split-pencil.md#forcing-three-affine-heads)

With $K=81/100$, the weighted variance caps at $b=2,3,4$ are respectively **1656826, 8426792 and 20841576**. The largest coordinate branch bound is 3892314127, below the first prime characteristic. For a value-linear factor, take any 2048 of its labels. On a site where the substituted received line is not identically zero, at most $m$ labels agree. The identity sites therefore number at least $t_*-mn/2048$. At each identity site all but at most $m$ labels agree, after the usual removal of coordinate content and leading-coefficient exceptions. The $m+1$ selected sections with the fewest misses each miss at most $mn/(2048-m)$ identity sites. Any three of these sections consequently share more than $d$ agreements, because $t_*-\lfloor mn/2048\rfloor-3\lfloor mn/(2048-m)\rfloor=327089236>d$. Their polynomial points lie on a single actual secant. The restriction of the factor to that secant has more than $m$ distinct roots and is zero. [Identity-site secant test](three-rates-two-head-window.md#common-factors-and-the-remaining-intersections)

Assign each selected label to one factor. Call a factor rich if it is value-linear and has at least 2048 assigned labels. At most two rich factors would give at most $2(480946858+1)+4\cdot20841576<n$ labels. With three or four rich factors, all are actual heads and positive-value degree is at most four. Three rich factors leave at most one other value-linear factor with at most 2047 labels. Four exhaust the degree. A rich head with core size $c_i$ and assigned population $L_i$ satisfies $(L_i-1)(t-c_i)\le e$ when $c_i<t=n-e$. Thus $c_i\ge t-\lfloor480946858/2047\rfloor$. Three such cores have total size exceeding $n+2d$ and are collinear over the rational-function field by the determinant bound. This holds for every rich triple.

Let $s$ be the degree of a primitive common direction of these heads. If $s=0$, all covered sites provide at most one distinct fresh label together. The core union $U$ has size at least $3(t-\lfloor480946858/2047\rfloor)-3d$ by inclusion-exclusion on any three heads. The upper bound $1+4(n-|U|)+2047<n$ rules out a constant direction.

## Counting four rich heads

Write $J$ for the fresh incidences of assigned labels on four rich heads and $E_{i\ell}$ for sites of equality between the two polynomial head values. At an uncovered site at most four labels can obtain a fresh agreement. At a covered site having $r=1,2,3$ coincident matches with the received pair, at most one assigned label can obtain a fresh agreement along the common direction. There $2r+1\le4+\binom r2$. At $r=4$ there are no fresh incidences. Summing the site bounds gives
\[
 2\sum_i c_i+J\le4n+\sum_{i<\ell}|E_{i\ell}|\le4n+6(d-1).
\]
The last inequality uses $s\ge1$. For $u_i=\max(0,t-1-c_i)$, each assigned label needs at least $1+u_i$ fresh sites and $c_i\ge t-1-u_i$. Thus the four-head population is at most $4n+6(d-1)-8(t-1)$. This is at most $n$ for $j\le22369620$ and at most $n+6j$ through the terminal predecessor.

## Translated deficit and matching construction

For three rich heads set $A=\sum_{i<\ell}(d-|E_{i\ell}|)$, let $R$ count common triple coincidences, and let $L$ be their assigned population. The three-head site count gives
\[
 6(t-1)+L+\sum_i(L_i-2)u_i+2A+3R\le3n+6d.
\]
The direction degree satisfies $A\ge3s$. If $L>n+6j$, the same seven units of slack arise at every $j$. They force $A=3$, $s=1$, $R=0$, every $u_i=0$, and $L\le n+2+6j$. The three scalar differences along the primitive direction therefore yield the same degree-$d-1$ pencil with disjoint full fibers required at $j=0$. This proves the necessity once cases with an outsider are bounded. [Three-head local count](quarter-successor-split-pencil.md#seven-units-of-slack)

Suppose there is a selected label outside the three heads. On its agreement support $T$, each of the three head polynomials at that label agrees at most $d$ times with the witness polynomial. There are at most $e$ sites outside $T$. Each of them belongs to at most two cores except at joint triple coincidences. Hence
\[
  3(t-1)-u \le \sum c_i\le 3d+2e+R,\qquad u=\sum_i u_i.
\]
In particular $R+u\ge178956964-5j$, still **11184814** at the terminal predecessor. In the three-head count above, $A\ge3$ and each $L_i-2\ge2046$, so $L\le n+2+6j-3(R+u)$. Adding all 2047 possible outsiders gives a total of at most $n-536868843+21j$. This is below $n+6j$ throughout the bracket and at most $n$ through $j=25565183$. Together with the four-head count, this eliminates every exception to the stated equivalence.

Conversely, given those three full fibers, receive the coincident head at each of their $3(d-1)$ sites. Among the all-distinct sites leave $1+3j$ holes and assign $89478487-j$ ordinary sites to each of the three heads. Each head has $t-1$ core agreements. The heads $(Xf,f)$ for $f=0,P,Q$ give a different ordinary label at every covered site and three mutually fresh labels at each hole. The field is large enough for the simultaneous avoidance construction because $(n+2+6j)^2$ is below its order. The ordinary and exceptional counts sum to $n+2+6j$. Lean constructs the witness for the full allocation range $0\le j\le89478487$; the equality with the worst case above runs through the known attack predecessor.
