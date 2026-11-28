# Half-rate lists at 353/500 agreement

At every positive length $n$, on every injective grid, at every positive interleaving width, at most **1,000,016** words of degree at most $n/2$ can agree with a center on **$353n/500$** sites, in characteristic zero or prime characteristic $p>20000$. The error fraction is $147/500$. At the two designated length-$2^{30}$ fields, every center is therefore safe through **315,680,096 errors** at the sponsor's budgets. The earlier length-independent result gives a smaller list of 19,999 at the higher agreement $181/256$ and requires only $p>425$. [Exact verifier](../../../scripts/probes/probe_half_joint_occupancy.py) · [Earlier uniform theorem and source counts](half-list-uniform-length.md)

## Interpolation and common-site orders

Put $R=1/2$, $s=353/500$, $L=500000$. Scalarize the words into a rational function field, preserving all true agreements, and extend scalars to its algebraic closure. Give $X,Y,V$ weights $1/n,R,R$. Use primary order 12 and derivative cap two at strict weight $12s$. The normalized source is larger than the local condition count, and the total degree over $k(X)$ of the primary in $Y,V$ is at most $b_0=16$. Factors independent of $V$ account for at most sixteen words. There are at most two positive-derivative factors. It suffices to rule out a group of $L$ words on any one irreducible positive-derivative factor $g$. For $g=V$ each difference of its solutions has zero derivative, so a distinct pair has at most $Rn/p$ shared sites in positive characteristic and none in characteristic zero. The occupancy second moment excludes this group. [Scalarization, quotient source, and zero-derivative case](half-list-uniform-length.md)

Use a primitive $g$ of weight $D$, with $v=\deg_V g\in\{1,2\}$. Write $A_v$ for its top $V$ coefficient, $a=\deg_Y A_v$, $b=\lfloor 2D\rfloor$, and $e=D-vR$. At a physical site $(x,y)$ write $o$ for the order in $U$ after $(X,Y,V)=(x+U,y+U z,z+U z_1)$. The local order is at most $b+v$. Let $p_x$ be the fraction of a retained group assigned to this site, allowing fractional membership on true hits so each word has exactly $sn$ mass. Remove the generic intersections of $g$ with $g_V$, and the words annihilating a nonzero $Y$-derivative of $A_v$ of orders $0$ through $a$. Even with overlap these deletions cost at most $3b_0^2$ words by Bézout and root counting over $k(X)$. All secondary interpolants below are evaluated on the original group.

For ordinary expectation over physical sites there are the bounds
$$
\mathbb E p_x=s,\qquad
\mathbb E[p_x(o-1)_+]\le D-R,\qquad
\mathbb E\!\left[(p_x-s)^2+{\bf1}_{o\le1}\,p_x^2/(o+v)\right]
 \le R-s^2+(2s-R)/(L-3b_0^2).
$$
The middle estimate evaluates the nonzero $g_V$ and uses its local order at least $o-1$. For $o=0$, $g(x,y,V)$ is a nonzero polynomial and bounds the number of hitting slopes by $v$. For $o=1$ that polynomial vanishes identically, so the order-one term is the nonzero polynomial $g_X(x,y,z)+z g_Y(x,y,z)$ of degree at most $v+1$. Thus on either type of site a pair of words with the same one of those slopes shares an additional root with multiplicity. The sum of the squares of the slope-class masses is at least $p_x^2/(o+v)$. After counting distinct ordered pairs, the two diagonal corrections sum to at most twice the selected mass. This gives the last estimate. [Local substitution and ordinary occupancy estimate](half-list-coefficient-derivatives.md)

## Quadratic coefficients and the extra local intersection

For $v=2$, write $g=A_0+A_1 V+A_2 V^2$ and put $S=Y-y$. If $o\ge2$ and $m=o-2$, the coefficients of $z_1^2,z_1,1$ show successively that $A_2,A_1,A_0$ have ordinary multiplicity at least $m$ at $(x,y)$. Write $a_i$ for their homogeneous terms of degree $m$ and $a'_i$ for those of degree $m+1$. The constant and linear terms in $z_1$ after substitution give
$$
 U^2a_0+USa_1+S^2a_2=0,\qquad Ua_1+2Sa_2=0,\qquad
 U^2a'_0+USa'_1+S^2a'_2=0 .
$$
Here $U$ is relatively prime to $S$. Eliminating $a_1$ gives $U^2\mid a_2$ and the last identity gives $U\mid a'_2$. In particular $a_2$ has $S$-degree at most $m-2$ and $a'_2$ at most $m$. [Lean check of the two divisibilities and the syzygy](../../../ArkLib/Research/ProximityGap/Frontier/PrimeHDSyzygyResultant.lean)

For every true hit, put $r=o-j$ for $0\le j\le a$. The order of $\partial_Y^j A_2(X,f)$ is at least
$$
 \Phi_j(o)=\max(0,r-2,{\bf1}_{r\ge1},2{\bf1}_{r\ge3}).
$$
Ordinary multiplicity supplies $r-2$. For $r=3$ the degree-$m$ term disappears under $j=m-1$ derivatives, leaving order at least two. For $r=2$ that term also disappears. For $r=1$ both displayed homogeneous terms disappear. At $o=1$ the value of $A_2$ vanishes directly. These bounds also apply to the evaluations on the constant graph $Y=y$. In particular each coefficient of $A_2$ in powers of $S$ is divisible by $U^{\Phi_a(o)}$, since $j!$ is a unit and $\Phi_j(o)\ge\Phi_a(o)$.

Choose a generic constant $t$ with $A_2$ coprime to $A_0+tA_1$. Primitivity as a polynomial in $V$ ensures this for all but finitely many $t$. The local intersection length is at least
$$
 (o-2)_+^2+(o-4)_+ .
$$
In the quotient by $(U,S)^{2m}$ the usual colength estimate is $m^2$. For $m\ge3$, there are at least $m-2$ further independent kernel vectors among the degree-below-$m$ multipliers of these two equations. Namely $(S^2-2tUS,-U^2)$ times any homogeneous polynomial of degree $m-3$ kills the degree-$m$ terms modulo $(U,S)^{2m}$, by the preceding identities. The first claim follows even if the degree-$m$ terms all vanish. The weighted resultant bounds the total intersection length by $n[aD+be-abR]$. This includes a coefficient independent of $Y$, where coprimality still supplies a nonzero resultant if the other has positive $Y$-degree. [Truncated local algebra and weighted Sylvester estimate](linear-contact-quotient.md)

For $v=1$ use the established local charge $(o^2-o-1)_+$ and $\Phi_j(o)=\max(0,o-j-1,{\bf1}_{o>j})$. For either $v$, let $H=\Phi_a(o)$. If $h_x$ is the order of the common $X$-content of $A_v$ then $h_x\ge H$. Removing this content from $\partial_Y^j A_v$ gives an order of at least $(\Phi_j(o)-h_x)_+$ at a hit. Since $h+p_x(\Phi_j(o)-h)_+$ is nondecreasing in $h$, the sum of the content degree and the remaining evaluated degree gives
$$
             \mathbb E[H+p_x(\Phi_j(o)-H)]\le e-jR .
$$
Taking $j=a$ counts the univariate leading coefficient at all sites. [Linear coefficient charges and content accounting](half-list-coefficient-derivatives.md)

## Combining the inequalities without rounding the occupancy

The secondary order is 20,000. The normalized quotient source gives a lower bound $Z_v(D,h)$ on $\mathbb E o$ for every tested derivative cap $h$. The original $L$ distinct jets exceed the product $b_0\lfloor 20000s/R\rfloor$ of the primary and secondary total degrees. The local rank formula is valid under the stated characteristic hypothesis. [Quotient lower bound and exact rounding of source dimensions](half-list-uniform-length.md#capturing-a-large-group)

For a fixed pair $(a,b)$ the site costs above are polynomials of degree at most two in $p_x$. Their upper bounds are affine in $D$. The verifier takes nonnegative rational combinations of those costs. For every integer $0\le o\le b+v$ it maximizes $o$ minus their combined cost on the **entire real interval** $0\le p_x\le1$, using the endpoints and any interior quadratic maximum. The largest of these remainders is a valid intercept. The coarser coefficient and variance bounds from the earlier proof also supply affine upper bounds. On each interval a single upper bound and a single cap $h$ give $\mathbb E o<Z_v(D,h)$ at both endpoints, and the gap is concave in $D$. A finite mesh and floating-point arithmetic only propose multipliers. All signs, maxima, and final inequalities are checked in rational arithmetic.

The verifier covers 143 linear and 121 quadratic intervals. The minimum normalized gaps exceed $10^{-6}$ and $0.0106$ respectively. No positive-derivative factor carries $L$ words, proving the claimed $2L+16$ list cap. The full theorem is a written proof with a rational certificate.
