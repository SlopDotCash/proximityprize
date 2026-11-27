# Hermite agreement coordinates for quarter-rate lists

On every injective grid of length $n=2^{30}$ over the second named prime, every closed ball of **536,870,931 errors** has at most $2n$ words at every positive interleaving width. Thus the first failing error count is at least **536,870,932**. The argument uses ordinary agreement multiplicities of complementary pairs a second time, on the sites where the rational center is exceptional. [Exact inequalities and finite-field controls](../../../scripts/probes/probe_quarter_list_residual_jets.py)

Put $d=n/4-1$, $j=17$, $t=2d-j$, $r=n-2t=38$. Suppose $m=2n+1$ distinct degree-at-most-$d$ words have at least $t$ agreements each. Positive interleaving width $w$ is covered by identifying a column in the base field to the power $w$ with an element of its degree-$w$ extension and using the same basis on coefficient columns. We work over the algebraic closure of the base field. [Scalar extension](../../../ArkLib/Research/ProximityGap/Frontier/ListScalarExtension.lean)

## Two anchor pairs and the common pencil

Choose $t$ agreement sites per word. In the [spectral deficit argument](spectral-deficit-list.md) put $a=t-d$, $L=1+m(nd-t^2)/(na)$ and $Q=2L(L-1)(L+1)^2$. Its nonnegative symmetric matrix $D$ has zero diagonal and off-diagonal entries $(d-|S_i\cap S_j|)/a$. We have $S=\operatorname{tr}D^2\ge m$, $\|D\|\le L$ and $\operatorname{tr}(D^2-I)^2\le Q<m$. These three estimates use no upper entry cap. The repeated-index fourth trace bound gives $S-\sum D_{ij}^4\le Q$.

Set $c=a/d$ and $D'=cD$, so every entry of $D'$ lies in $[0,1]$. Since $|S-m|\le\sqrt{mQ}$, the total ordered square mass on entries of $D'$ at most $\mu=1-h/d$ is at most
$$
 \frac{Q+2m(1-c^2)}{1-\mu^2}.
$$
Indeed $\sum (D'_{ij})^2(1-(D'_{ij})^2)=c^4(S-\sum D_{ij}^4)+c^2(1-c^2)S$. Thus there are at least half of $c^2m$ minus half of the displayed bound unordered edges with overlap below $h$. At $h=63,100,000$ this gives more than 942,196 edges. Each vertex belongs to at most $L^2/\mu^2<35,933$ edges by the squared Euclidean norm of a column. In particular two disjoint anchor edges exist. Every tight edge misses at most $s=r+h-1=63,100,037$ sites, counting its chosen agreement sets.

At $h'=140,000,000$ there are more than 496,524,830 edges. Each misses at most $r+h'-1$ sites. For a pair $i$ of polynomials $f_i,g_i$ set $S_i=f_i+g_i$, $P_i=f_i g_i$. The two anchor sums differ since equal sums force equal products on $n-2s>2d$ sites. The determinant of their two rows $(1,S_i,P_i)$ and the row of any loose edge vanishes on $n-2s-(r+h'-1)>3d$ common covered sites and has degree at most $3d$. All these edges therefore belong to the polynomial pencil
$$
 S_i=S_0+AU_i,\qquad P_i=P_0+BU_i,\qquad (Af_i-B)(Ag_i-B)=N
$$
with $A\ne0$, $\gcd(A,B)=1$, $N=B^2-AS_0B+A^2P_0\ne0$. The two disjoint anchors imply $N\ne0$, since otherwise every pair contains the rational function $B/A$ as a word. Distinct unordered edges give distinct polynomial parameters even when the loose edges were counted before establishing disjointness. Indeed the parameter determines the pair's monic quadratic. The four cross-differences of any two pairs multiply to $N(U_i-U_j)^2$, hence $\deg N+2\deg(U_i-U_j)\le4d=n-4$. [Pencil identities](complementary-list-pencil.md)

Let $E$ consist of the physical sites with $N(x)\ne0$ or $A(x)y(x)\ne B(x)$ and write $e=|E|$. As in the pencil argument, the two anchors imply $e\le4s-4$. On each exceptional site at most one scalar parameter value can cover the center. Every tight edge covers at least $e-s$ exceptional sites. The degree of any parameter difference is at most $(e-4)/2$, since $N$ has at least $n-e$ distinct roots. Applying Cauchy–Schwarz to the tight parameters' chosen $e-s$ exceptional hits gives the necessary inequality
$$
 M_s\big((e-s)^2-e(e-4)/2\big)\le e\big(e-s-(e-4)/2\big)
$$
when $e>s$ and the left parenthesis is positive, with $M_s=942,196$. This follows first with the actual intersection cap, then with the larger $(e-4)/2$ by monotonicity. The inequality fails for every $e\ge218,000,000$. For example, after moving all terms to the left, the quadratic has positive leading coefficient and both its value and its derivative are positive at that endpoint. Thus $e\le218,000,000$.

## Counting true agreements as weighted coordinates

Take all the loose-edge parameters and set $u=\max_i\deg U_i$, using the anchor parameter $U_0=0$. Then $\deg N+2u\le n-4$ and $h_0=e-4-2u\ge0$. At an ordinary site $x\notin E$, $A(x)\ne0$ and $N(x)=0$, so every pair scores at least one true agreement. A double agreement forces a multiple zero of $N$ by its product identity and the fixed parameter value $U_i(x)=(2y-S_0)/A$. There are $q\le h_0$ ordinary sites where $N$ has a multiple zero, by counting its degree after its $n-e$ ordinary roots. Make one coordinate of weight 1 at each such site, marked for the pairs with a double agreement.

At $x\in E$ a covering pair must solve $(B-Ay)U_i=S_0y-y^2-P_0$. If $B-Ay=0$ there are no covering pairs, since $A\ne0$ and the right side times $-A^2$ equals $N(x)\ne0$. Otherwise there is one required value $w_x$. Any pair with this value covers $y$. When $S_0+Aw_x=2y$, it scores two agreements there. In this case mark a coordinate of weight 2 precisely when $U_i(x)=w_x$. For all other exceptional sites use a coordinate of weight 1, marked exactly upon a true agreement. Let $b$ be the number of weight-1 exceptional sites.

A shared weight-2 mark uses two root multiplicities of $U_i-U_j$. In fact put
$$
 F(X,Z)=(S_0+AZ)^2-4(P_0+BZ).
$$
At the marked site $F(X,U_i)=(f_i-g_i)^2$ has a double zero, whereas $F_Z(x,w_x)=4(Ay-B)\ne0$. Differentiation gives the *same* derivative $U_i'(x)=-F_X(x,w_x)/F_Z(x,w_x)$ for every covering parameter. This also applies at poles of $B/A$. At each weight-1 coordinate a shared mark uses at least one root of the parameter difference. Consequently, the total weight common to two distinct mark sets is at most $u$.

The square divisibility also has a characteristic-independent proof. At a shared double, write $y_0=y(x)$ as a constant. Each of $(f_i-y_0)(g_i-y_0)$ and $(f_j-y_0)(g_j-y_0)$ is divisible by $(X-x)^2$. Their difference is $(B-y_0 A)(U_i-U_j)$, and the first factor is a unit at $x$. Taking the product of the coprime point factors gives the weighted intersection bound. Lean checks both the square divisibility and the sum of weights for any finite set of shared marks. [Formal proof](../../../ArkLib/Research/ProximityGap/Frontier/ComplementaryListPencil.lean)

There are $K=e+q$ coordinates and their total weight is $W=2e-b+q$. Each pair marks weight at least $v=e-r$, since its total true agreement count, including both words at a double, is $n-e$ plus this weight and is at least $2t$. Represent a mark set by the real unit vector with coordinates $\pm\sqrt{w_x/W}$, positive exactly on its marks. Two different parameters give dot product at most
$$
 \frac{W-4v+4u}{W}=\frac{144-2h_0+q-b}{W}.
$$
Call this integer numerator $g$. If $g\le-2$, nonnegativity of the squared norm of the sum gives $M\le1+W/2\le1+3e/2<496,000,000$. Otherwise $g\ge-1$ forces $q\le h_0\le145$ and $W\ge2e-145$. For $e\ge20,000$ each dot product is therefore at most $73/K$, since $144(e+145)/(2e-145)\le73$. We have at least $496,000,000$ vectors.

## Three size ranges for the real vectors

For $20,000\le e\le4,000,000$, take $s_1=73/K$, $a_1=1/73$ and $P(z)=(z-s_1)(z+a_1)^2$. Its off-diagonal evaluations are nonpositive. For unit vectors the matrices with entries $z^l$ for $l=1,3$ and $z^2-1/K$ are positive semidefinite by their tensor Gram representations (subtract $I/K$ from each quadratic tensor). The coefficients of these kernels in $P$ are nonnegative since $K\ge20,000>2\cdot73^2$. Its remaining constant coefficient is $(1-73^2/K)/(73K)$. Thus $M\le P(1)73K/(1-73^2/K)<103K<496,000,000$.

For the other two ranges take a subset of $m'$ unit vectors with Gram matrix $G$ and put
$$
 D_1=I+(s_1 J-G)/(1-s_1).
$$
The latter formula has diagonal zero. It is entrywise nonnegative and has operator norm at most $L_1=1+m's_1/(1-s_1)$ by the upper Rayleigh bound and entrywise absolute values. Its complement $I-D_1$ has rank at most $K+1$. Cauchy–Schwarz on its eigenvalues gives $\operatorname{tr}D_1^2\ge (m')^2/(K+1)-m'$. The nonnegative third trace, followed by the identity $D_1-I=(s_1 J-G)/(1-s_1)$, gives
$$
 m'\left(\frac{m'}{K+1}-2\right)
 \le\operatorname{tr}\big((D_1-I)(D_1+I)^2\big)
 \le (L_1-1)(L_1+1)^2 .
$$
The upper bound uses positivity of the trace of $G(D_1+I)^2$.

If $4,000,000\le e\le110,000,000$, use $m'=4(K+1)$. There are enough vectors and $L_1-1<293$. The left side is at least $32,000,000$, whereas $293\cdot295^2<26,000,000$. If $110,000,000\le e\le218,000,000$, use $m'=\lceil11(K+1)/5\rceil$. This uses fewer than $480,000,000$ vectors and gives $L_1-1<162$. The left side exceeds $48,000,000$, whereas $162\cdot164^2<4,400,000$. Both ranges are impossible.

Finally $e<20,000$ supplies the [moving-section interpolation proof](quarter-list-moving-jets.md) with parameter degree at most $9,998$, at most $19,996$ multiple roots and moving-section height at least $536,850,914$. Use bidegrees $(16,4)$, an interpolation matrix of rank threshold 83, and 82 contact sections. The doubled contact surplus is $6,708,575,990$. The derivative resultant has coefficient degree below the height floor. An irreducible factor contains at least $24,800,000$ parameter jets while the differential Bézout bound is $7,998,800$. As the second named prime exceeds $2\cdot9,999$, the local odd-pole derivative contradiction applies. [Differential argument](quarter-list-jet-derivation.md)
