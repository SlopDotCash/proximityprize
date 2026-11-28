# Coefficient contacts for the second-prime eighth-rate list

At the second named prime, every closed ball of **709,206,474 errors** contains at most $2n$ words at rate $1/8$ and length $n=2^{30}$. This holds on every injective grid and at every positive interleaving width. The first failing error count is at least **709,206,475**. The exact first failure remains open. [Exact finite verifier](../../../scripts/probes/probe_eighth_quadratic_coefficient_contacts.py)

Write $d=n/8-1$, $t=\lceil679n/2000\rceil=364,535,350$, $s=t/n$ and $R=d/n$. Scalarization puts the list in one polynomial ring over an extension of the named field. Use weights $1,d,d-1$ on $X,Y,V$, and let $N(w,h)$ and $C(r,h)$ denote the strict weight dimension and local contact rank. At primary order $10$ and derivative cap $4$ we have $N(10t,4)>nC(10,4)$. An interpolant of weight below $10t$ contains all candidate jets and has total $(Y,V)$ degree at most $b=\lfloor(10t-1)/(d-1)\rfloor$. Assign each candidate to an irreducible factor that contains its jet. The factors independent of $V$ account for at most $b$ words. Form $g$ from the distinct factors of positive derivative degree assigned at least $L=n/8$ words. Write $v=\deg_Vg$ and $D$ for its weight. Outside these large groups there are at most $(4-v)L+b$ words. [Local interpolation and scalarization](sixteenth-list-quotient-jets.md) · [Grouping and the adaptive board](sixteenth-list-joint-quotient.md)

## Contacts of the quadratic coefficient

Assume $v=2$ and write $g=A+BV+CV^2$ with $a=\deg_Y C$. At a received point $(x,y)$ put $U=X-x$, $S=Y-y$. Write $o$ for the $U$-order under $S=Uz$, $V=z+Uw$. If the coefficient of $U^iS^j$ in $C$ is nonzero, then
$$
                o\le j+i+\min(i,2).                                      \tag{1}
$$
Indeed the term $U^iS^jV^2$ occupies block $(i+j,j+2)$ of the local expansion. Its possible companion terms are $U^{i-k}S^{j+k}V^{2-k}$ for $0\le k\le\min(i,2)$. Coefficients of $w^\ell$ have the factors $\binom{2-k}{\ell}$. The first $1+\min(i,2)$ binomial rows form an invertible matrix on these columns since the characteristic exceeds $2$. A nonzero top coefficient forces a nonzero row of order at most the right side of (1).

Define $\phi_j(o)=\min\{i\ge0:j+i+\min(i,2)\ge o\}$. Increasing $j$ by one lowers $\phi_j$ by at most one. Write $C_j=\partial_Y^{[j]}C$ for the ordinate Hasse derivative. If $f(x)=y$, every term contributing to $C_j(X,f(X))$ from ordinate power $\ell\ge j$ has order at least $\phi_\ell(o)+\ell-j\ge\phi_j(o)$. For $j=a$ this derivative is a nonzero polynomial in $X$ alone, so the same bound holds at every site. All $C_j$ are nonzero because the characteristic exceeds $a$. For $j<a$ at most $a-j$ words make $C_j(X,f)$ identically zero, by root counting over $k(X)$.

Take one large group, and discard its words on $g_V=0$ and on any of these $C_j=0$ identically. Squarefreeness makes $g_V$ coprime to each large factor over $k(X)$, giving at most $b^2$ losses by Bézout. The other losses sum to at most $a(a+1)/2\le b^2$. At least $M_0=L-2b^2$ words remain in the group. Choose exactly $t$ true hits for each retained word, let $p$ be the fraction choosing the given site and average over the $n$ sites. The bounds apply to each group individually. With $E=(D-2(d-1))/n$ they give
$$
 \mathbb E\phi_a(o)\le E-aR,\qquad
 \mathbb E[p\phi_j(o)]\le E-jR\quad(0\le j<a).                       \tag{2}
$$
The evaluated univariate derivatives have degree at most $D-2(d-1)-jd$.

At any site with $o\le1$ at most three slopes occur among the hitting words. For $o=0$ the nonzero polynomial $g(x,y,z)$ in the slope $z$ has degree at most two. For $o=1$ the constant term vanishes identically, so all three coefficients of $g(x,y,V)$ vanish. The coefficient of $U$ after substitution is then independent of $w$, nonzero, and has degree at most three in $z$. Every horizontal word through the point gives a root of this polynomial.

Write $M\ge M_0$ for the retained population. In ordered sampling of pairs of words, a common chosen site contributes at least one root multiplicity to the difference. At $o\le1$ a common chosen site with the same slope contributes one additional multiplicity. The sum of squared slope frequencies is at least $p^2/3$ there. Removing the diagonal costs at most $2p/M$ at a site, and every off-diagonal pair has total multiplicity at most $d$. With $\mathbb E p=s$ this yields
$$
 \begin{aligned}
 \mathbb E(p-s)^2&\le R-s^2+(s-R)/M_0,\\
 \mathbb E\big[(p-s)^2+p^2\mathbf1_{o\le1}/3\big]&\le R-s^2+(2s-R)/M_0 .
 \end{aligned}                                                        \tag{3}
$$
For the first bound count only the common chosen sites and restore the diagonal once. The evaluated derivative $g_V$ also gives $\mathbb E(po)\le s+(D-d+1)/n$, since its order on a hit is at least $o-1$. The local estimate $o\le D/d+2$ follows by taking a nonzero coefficient in $g(x,Y,V)$ and separating its at most three columns as in (1). No fiber $X-x$ divides this product. [Order and derivative bounds](sixteenth-list-quotient-jets.md#bounding-the-mean-contact-order)

## Excluding all quadratic products of middle weight

Use uniform secondary order $r=6000$. If a product of large factors exists, for each secondary cap $h\ge2$ its mean contact order must satisfy
$$
 \mathbb E o\ \ge\ Z(D,h)=
 \frac{N(rt,h)-N(rt-D,h-2)-n[C(r,h)-C(r,h-2)]}
      {n[C(r,h-2)-C(r-1,h-2)]}.                                       \tag{4}
$$
Successive increments of $C$ are nondecreasing by multiplication by $U$ on the associated graded pieces. A strict opposite inequality therefore gives a secondary polynomial of weight below $rt$ vanishing on the jets of all large groups and coprime to at least one large factor. By plane Bézout that factor contains at most $b\lfloor(rt-1)/(d-1)\rfloor<M_0$ words. [The local quotient proof](sixteenth-list-quotient-jets.md#the-local-quotient)

For $4(d-1)\le D\le6d-2$ the leading degree $a$ ranges from zero to four. At each $a$ begin the interval at $\max(4(d-1),(a+2)d-2)$. The verifier splits this integer interval into 32 pieces. On each piece it chooses a single cap $h\in\{300,600,\dots,6000\}$ and one rational linear combination of (2), (3), the derivative bound and $\mathbb E(p-s)=0$. Its coefficients on all inequalities are nonnegative. The constant that majorizes $o$ pointwise is computed by maximizing the difference over each integer $o\le\lfloor D_{\rm right}/(d-1)\rfloor+2$ and $0\le p\le1$. For fixed $o$ this is a concave quadratic in $p$ and its maximum is rational. The resulting upper bound on $\mathbb E o$ is affine in $D$. The function $Z(D,h)$ is concave because $N(rt-D,h-2)$ is a sum of positive parts of affine functions. Exact checks at both endpoints of every piece prove the strict opposite of (4) throughout the interval. The verifier contains all the dual coefficients and uses only rational and integer arithmetic.

## All remaining factors

For $v=2$ and $D\ge6d-2$, and for $v=3,4$ and $D\ge4(d-1)$, the existing joint adaptive interpolation excludes the product using the parameters below. Use 80 variance intervals and the shared upper endpoint $10t-1$. [Adaptive interval inequalities](joint-list-contact-boards.md#products-of-derivative-degree-two-or-three)

| $v$ | Order | Secondary cap | Occupancy slope | Base curvature | Increment curvature |
|---:|---:|---:|---:|---:|---:|
| 2 | 10000 | 3000 | 24900 | 6.204 | .229 |
| 3 | 4000 | 1000 | 10200 | 9.763 | .166 |
| 4 | 4000 | 1000 | 10200 | 13.02 | .166 |

A surviving product with $v=2,3$ has total $(Y,V)$ degree at most three. The normalized differential-curve bound summed over its factors, plus $(4-v)L+b$, fits $2n$. The support of four derivative factors has minimum weight $4(d-1)$ and was already excluded. When $v=1$, the coefficient intersection estimate with ordinary secondary order $3000$ excludes $D\ge7d-1$, giving total degree at most six. Its contribution is at most $\max(6+10d,(n-d)/(t-d))$, which fits the budget with $3L+b$ more words. Finally $4L+b\le2n$ covers the case with no large factor. The named characteristic exceeds all degree and regularity requirements of these arguments. [Normalized curve count](first-order-normalized-curve.md) · [Linear coefficient comparison](linear-contact-quotient.md)

Run the finite certificate with `python3 scripts/probes/probe_eighth_quadratic_coefficient_contacts.py`.
