# Reed–Solomon line-MCA error as the dimension increases

Fix a finite field of size $q$, an injective evaluation domain with $n$ sites, and an agreement
threshold $t=\lceil(1-\delta)n\rceil$. Whenever $1\le k\le K<t$, the worst-case line-MCA
error for dimension $k$ is at most the error for dimension $K$. The assertion applies to the
literal folded-codeword and joint-agreement event on a common witness set.
[Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/DimensionMultiplierMCA.lean)

## One multiplier preserves all bad labels

It suffices to increase $k$ by one. Fix the received rows $u_0,u_1$ and choose one witness
set $S_z$ for each bad label $z$. Multiply both rows at each site $x$ by the same affine
polynomial $a+bx$. Every old folded witness polynomial becomes a polynomial of degree below
$k+1$ by the same multiplication.

For each $z$ the pairs $(a,b)$ that allow both multiplied rows to fit polynomials of degree
below $k+1$ on $S_z$ form a vector subspace of the coefficient plane. This subspace is
proper. Otherwise take the multipliers $1$ and $X$. For each original row $y$ there would
be degree-at-most-$k$ polynomials $P,Q$ agreeing with $y$ and $Xy$ there. Since
$|S_z|>k+1$, the polynomial $XP-Q$ vanishes identically. Hence $P$ has degree below $k$,
giving the forbidden original joint agreement.

There are at most $q$ bad labels. Their proper subspaces cover at most $q(q-1)$ nonzero
pairs, strictly fewer than $q^2-1$. A single multiplier outside the union therefore preserves
every old bad label on its original support. Taking the worst case over stacks and iterating
proves the stated monotonicity. The same argument allows a multiplier to vanish at a site,
since the subspace test directly enforces joint disagreement.

## Why the strict support bound matters

For every injective $n$-site domain over $\mathbb F_q$ with $n\ge3$, take $t=n-1$. The worst-case
error drops from exactly $n/q$ at dimension $n-2$ to exactly $1/q$ at dimension $n-1$.

At dimension $n-2$ each $(n-1)$-site restriction has codimension one. It can witness at most one
bad scalar: two distinct scalar fits on that restriction solve linearly for both rows. If the
whole domain witnesses badness, at least one $(n-1)$-site restriction witnesses it as well.
Indeed, if all restrictions admit joint fits, the interpolants of each row agree on the
$n-2$ common sites of any two restrictions and therefore coincide. This bounds the total by $n$.

For equality take the received rows $X^{n-1}$ and $X^{n-2}$. At the restriction missing $a$, the
monic vanisher has coefficient $-\sum_{x\ne a}x$ at degree $n-2$. Subtract this vanisher
from $X^{n-1}+zX^{n-2}$ at $z=-\sum_{x\ne a}x$, obtaining degree below $n-2$. The second
row cannot fit at that degree on $n-1$ sites. The $n$ omitted sites give distinct labels.
At dimension $n-1$ every $(n-1)$-site restriction admits joint fits. Only the full domain can
witness badness and its code has codimension one. The rows $0,X^{n-1}$ attain exactly one
bad scalar, namely zero. This establishes the sharp failure at $t=K$.

## Exact production interval

At length $2^{30}$ and security tolerance $2^{-128}$, the second named field has the same
first failing count **715,827,882** at **every** message dimension $2\le k\le2^{26}$.
This holds for every injective domain and every positive interleaving width. More generally
it holds over every prime field with $\lfloor p/2^{128}\rfloor=2^{31}$ and every finite field
in that budget class whose characteristic exceeds 1,744,830,589.

At the predecessor count the agreement threshold is 357,913,943, strictly greater than
$2^{26}$. Dimension monotonicity transfers the established safety bound down to dimension
two. At the next error count the construction with three disjoint cores uses only affine
heads. It exceeds the budget throughout the stated dimensions. Thus the safe real interval
is exactly $[0,715827882/1073741824)$.
[Operational classification](../../../ArkLib/Research/ProximityGap/Frontier/LowDimensionCubicPlateau.lean) ·
[Predecessor bound](../../../ArkLib/Research/ProximityGap/Frontier/UniversalCubicThreshold.lean) ·
[Successor construction](../../../ArkLib/Research/ProximityGap/Frontier/ManyHeadLocatorMass.lean)
