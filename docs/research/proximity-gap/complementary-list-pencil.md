# A rational center and a common pencil forced by a quarter-rate list

Set $n=2^{30}$, $d=n/4-1$, $t=2d$. Suppose $2n+1$ distinct polynomials of degree at most $d$ agree in at least $t$ places each with one received word $y$ on an injective $n$-point grid. Then there are coprime polynomials $A,B$, with $A\ne0$, and a nonzero polynomial $N$ such that outside **at most 3,080 sites** we have simultaneously $A(x)\ne0$, $y(x)=B(x)/A(x)$ and $N(x)=0$. At least **1,072,766,345 disjoint pairs** from the list belong to one polynomial pencil
$$
 f_i+g_i=S_0+A U_i,\qquad f_i g_i=P_0+B U_i,\qquad
 (A f_i-B)(A g_i-B)=N.
$$
Here $\deg A\le d$, $\deg B\le 2d$ and the distinct polynomial parameters $U_i$ have degree **at most 1,538**. Over the second named prime this is a necessary condition for list failure at the quarter-rate count of 536,870,914 errors. All conclusions apply at positive interleaving width by identifying the alphabet with a scalar extension. The [moving-section proof](quarter-list-moving-jets.md) excludes this family on the second named prime. [Scalar extension](../../../ArkLib/Research/ProximityGap/Frontier/ListScalarExtension.lean)

## Extracting the pairs

Choose any $t$ agreement sites per word. Put $m=2n+1$, and let $D$ be the symmetric matrix with zero diagonal and entries $D_{ij}=1-|S_i\cap S_j|/d$ off the diagonal. Distinct polynomial words intersect in at most $d$ chosen sites. Write $L=1+m(nd-t^2)/(nd)$. The centered incidence Gram bound gives $S=\operatorname{tr}D^2\ge m$ and $\operatorname{tr}(D^2-I)^2\le Q=2L(L-1)(L+1)^2$. [Fourth-moment proof](spectral-deficit-list.md)

For $0<\mu<1$, join $i,j$ when $D_{ij}>\mu$. Write $q_i=\sum_jD_{ij}^2$. Expanding the off-diagonal squares of $D^2$ and retaining their diagonal summands gives $\operatorname{tr}D^4\ge 2\sum_i q_i^2-\sum_{ij}D_{ij}^4$. Consequently $Q\ge S-\sum_{ij}D_{ij}^4$, since $2S^2/m-3S+m\ge0$. The weak edges carry ordered square mass at most $Q/(1-\mu^2)$. Each strong edge contributes at most two. Moreover the squared off-diagonal entries of $D^2$ give $Q\ge\mu^4\sum_i\deg(i)(\deg(i)-1)$, by counting all ordered paths with distinct endpoints. Removing one edge per conflicting pair of edges leaves a matching of size at least
$$
 \tfrac12\left(m-\frac{Q}{1-\mu^2}-\frac{Q}{\mu^4}\right).
$$
Take $\mu=1-h/d$. At $h=901$ this gives at least 1,182,724 disjoint pairs of overlap at most 900. Each covers all but $s=904$ sites, since $n-2t=4$. At $h=1,000,000$ the corresponding matching has at least 1,072,766,345 pairs, each missing at most 1,000,003 sites. The two matchings may be chosen independently. [Exact arithmetic and field controls](../../../scripts/probes/probe_complementary_list_pencil.py)

## The polynomial identities

Write $S_i=f_i+g_i$, $P_i=f_i g_i$. Wherever a pair covers the center, $P_i(x)=S_i(x)y(x)-y(x)^2$. Fix two pairs from the tighter matching. Their sums differ as polynomials. Otherwise their products agree at $n-2s>2d$ sites, so their monic quadratics are equal and have the same unordered roots. For each pair in either matching, the determinant of the three rows $(1,S_i,P_i)$ vanishes at more than $3d$ common sites, since $n-2s-1,000,003>3d$. Its degree is at most $3d$, so it vanishes identically. After dividing the two coefficient differences for the fixed pairs by their gcd, take $A,B$ to be their primitive direction. Euclid's lemma gives $S_i=S_0+A U_i$, $P_i=P_0+B U_i$ with $U_i$ polynomial, also when $B=0$. Two different unordered pairs have distinct parameters.

Define $N=B^2-S_0 A B+P_0 A^2$. The common-product identity follows by expansion. If $N=0$, every pair would contain $B/A$ as a polynomial word, contrary to the two disjoint fixed pairs. For distinct pairs in the *same* matching, their four cross-differences are nonzero and satisfy
$$
 (f_i-f_j)(g_i-f_j)(f_i-g_j)(g_i-g_j)=(U_i-U_j)^2N.
$$
Indeed, evaluating the difference of the two monic quadratics at either root $v$ of the second gives $(f_i-v)(g_i-v)=(U_i-U_j)(B-Av)$. The product has degree at most $4d=n-4$. In fact the identity and this upper bound hold for any two distinct parameters, as $N\ne0$. [Lean determinant and both factorization identities](../../../ArkLib/Research/ProximityGap/Frontier/ComplementaryListPencil.lean)

## Recovering the center

For the two fixed pairs write $w=\deg(U_i-U_j)$. On their at least $n-2s$ common covered sites the cross-product vanishes, whence $n-2s\le w+\deg N\le n-4-w$. Thus $w\le2s-4$. Outside the zeros of $U_i-U_j$, their common covered sites satisfy $Ay=B$ by subtracting their quadratic equations, and also $N=0$. Coprimality makes $A$ nonzero at each such site. The exceptional set $E=\{x:N(x)\ne0\text{ or }A(x)y(x)\ne B(x)\}$ therefore has size $e\le2s+w\le3612$.

There are at least $n-e$ distinct roots of $N$. The cross-product degree bound implies $2\deg(U_i-U_j)\le e-4$. Taking $U_0=0$ bounds the degrees of all parameters. At each exceptional site there is at most one parameter *value* for a pair covering $y$, by the linear equation
$$
 (B-Ay)U_i=S_0 y-y^2-P_0 .
$$
If its coefficient vanishes there, its right side is nonzero. Indeed $A\ne0$ when $Ay=B$ and $A^2(y^2-S_0y+P_0)=N\ne0$ at such an exceptional site.

Choose the required value at each exceptional site, arbitrarily if there is none. Each tight-matching parameter hits it at least $v=e-s$ times. For $e>s$ restrict each to $v$ chosen hits. Any two intersect at most $j=\lfloor(e-4)/2\rfloor$ times. For $M=1,182,724$ of the parameters, counting the ordered intersections gives $M(v^2-ej)\le e(v-j)$ by Cauchy–Schwarz on the $e$ sites. Exact integer substitution excludes every $3081\le e\le3612$. Thus the union of the two exceptional conditions has size at most 3080 and every parameter has degree at most 1538. In particular, on a smooth subgroup $N$ shares a factor of degree at least $n-3080$ with $X^n-1$. [Finite verifier](../../../scripts/probes/probe_complementary_list_pencil.py)

## A restriction on parameter cross ratios

Over either named prime, no ten distinct parameters in this pencil can have all their cross ratios constant in $X$. Work over the algebraic closure of the coefficient field. The polynomial $N$ has at least $n-3080$ distinct roots and degree at most $n-4$. In particular some root is simple. On the smooth projective curve $C$ with function field $K(X,\sqrt N)$, put
$$
 H=\frac{2B-AS_0+2\sqrt N}{A^2}.
$$
Its conjugate $H'$ is different. The discriminant of the monic quadratic in the ordinate with parameter $U_i$ gives
$$
 (H-U_i)(H'-U_i)=(f_i-g_i)^2/A^2.
$$
Normalize three distinct parameters $U_0,U_1,U_2$ by the unique fractional linear transformation $T$ over $K(X)$ taking them to $0,1,\infty$. Put $\phi=T(H)$, let $\sigma$ be the involution of $C$ over $X$, and let $D$ be the degree of $\phi$. The maps $\phi$ and $\phi\circ\sigma$ are distinct. If $T(U_i)=c$ is finite and constant, then $\phi-c$ is a scalar in $K(X)^\times$ times $(H-U_i)/(H-U_2)$. Its norm to $K(X)$ is a square. All these maps are tame at the named primes. For instance the degrees on $C$ of $X$ and $\sqrt N$ are $2$ and $\deg N$. The formula for $H$ and the normalization by three polynomials of degrees at most 1538 give $D<20n<p$ by adding the pole-degree bounds for products, quotients and sums.

Write $g$ for the genus of $C$. The maps $\phi,\phi\circ\sigma$ coincide at most $2D$ times counted with multiplicity, by taking their cross-difference in homogeneous coordinates. This count includes common poles. It also includes the $2g+2$ distinct ramification points of the separable quadratic map $X$, by Riemann–Hurwitz. In particular $g\le D-1$.

Consider all finite constant targets $c$ just obtained. A point in the fiber of $c$ of odd multiplicity cannot lie over a ramified point of $X$, since its valuation would be the valuation of the square norm. At an unramified point an odd valuation must be paired with another odd valuation above the same $X$. Thus either its conjugate has value $c$ or its conjugate is a pole. Across the disjoint fibers this allows at most $2D-(2g+2)+D$ odd points. If there are $r$ targets, the total ramification contributed by their fibers is at least half of $rD$ minus half the number of odd points, since $e-1\ge(e-\mathbf1_{e\ {\rm odd}})/2$ for every positive multiplicity $e$. Applying Riemann–Hurwitz to $\phi$ gives
$$
 rD\le 2(2g-2+2D)+3D-2g-2=7D+2g-6<9D.
$$
There are at most eight finite targets and one additional normalized parameter at infinity. Thus every ten parameters include a nonconstant cross ratio. The argument leaves open pencils with genuinely varying parameter cross ratios. The determinant and factorization identities above are machine-checked. The extraction, genus argument and rational-center estimate are written proofs.

## Recovering the forced polynomials from a proposed received word

There is a linear test on the received word alone. Solve $V(x)=U(x)y(x)$ on the whole domain with $\deg U\le d+3080$ and $\deg V\le2d+3080$. For a failing center the error locator multiplying $A,B$ supplies a nonzero solution. Any nonzero solution has $U\ne0$ by the root bound. On the at least $n-3080$ sites where $y=B/A$, the polynomial $AV-BU$ vanishes. Its degree is at most $3d+3080<n-3080$. Every nonzero solution therefore reduces to the *same* rational function $B/A$, even if the set of agreements was not supplied. Its poles on the grid and its discrepancies can now be counted directly. A trivial solution space, or more than 3080 discrepancies including poles, certifies safety for this center.

The polynomial $N$ is also uniquely determined by the center on **every injective domain**, after making $A$ monic. The information at infinity matters when $A$ has small affine degree. Here is a homogeneous linear recovery test. Write $G$ for the degree-$n$ domain vanisher in homogeneous coordinates $(X,Z)$. For a nonzero polynomial $C$ of degree at most $v$, use $C^{[v]}=Z^v C(X/Z)$ and set $0^{[v]}=0$. Let $\ell$ be the common order at infinity of $A^{[d]}$ and $B^{[2d]}$, that is, the smaller of their two vanishing orders. Infinite order is allowed for the zero polynomial. Then
$$
 A_* = A^{[d]}/Z^\ell,\qquad B_* = B^{[2d]}/Z^\ell
$$
are coprime binary forms of degrees $d-\ell$ and $2d-\ell$. They have no common affine zero by construction. The binary form
$$
 N_* = B_*^2-S_0^{[d]}A_* B_*+P_0^{[2d]}A_*^2
$$
has degree $4d-2\ell$. Since it vanishes at at least $n-3080$ different physical sites, necessarily $\ell\le1538$.

Remove the common factors of $G,N_*$ in the binary polynomial ring. Their remaining ratio gives $N_* K=G D$ with coprime homogeneous $K,D$, $\deg K=r\le3080$ and $\deg D=r-4-2\ell$. Padding both by $Z^{3080-r}$ produces a nonzero solution to the linear congruence
$$
       B_*^2 K\equiv G D\pmod {A_*},
       \qquad \deg K=3080,\quad\deg D=3076-2\ell .
$$
The zero form is allowed in these homogeneous coefficient spaces. Any two solutions satisfy $A_*\mid B_*^2(K_1 D_2-K_2 D_1)$ by multiplying the two congruences by $D_2,D_1$ and subtracting. Coprimality removes $B_*^2$. The cross-difference has degree at most $6156-2\ell<d-\ell=\deg A_*$, so it vanishes. In comparison with the true solution, this forces every nonzero solution to have both entries nonzero and give the same ratio. Thus one recovers $N_*=G D/K$ uniquely, without knowing any list word, error locator, or partition. The test requires two homogeneous linear systems and polynomial arithmetic. An invalid degree, a missing solution, or failure of exact division certifies safety for this center.

Every paired word yields a degree-$(2d-\ell)$ homogeneous divisor $A_* f_i^{[d]}-B_*$ of $N_*$. Its residue modulo $A_*$ is fixed. Since $A_*$ has positive degree and is coprime to $B_*$, at most one scalar multiple of any divisor can have that residue. Checking the complementary divisor and evaluating the resulting words uses only the candidate center and domain. Counting these divisors for arbitrary possible centers remains open. [Recovery controls](../../../scripts/probes/probe_complementary_list_pencil.py)
