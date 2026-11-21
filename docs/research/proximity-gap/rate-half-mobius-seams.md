# A bad rate-half radius strictly below one third at the first prize prime

Let $p=365375409332725729550921208179070755120141565953$, let $g$ be the repository’s certified generator of order $n=2^{30}$, and take the dimension-$k=n/2$ Reed–Solomon code on $H=\langle g\rangle$ over $\mathbb F_p$. At $a=(n-1)/3=357913941$ Hamming errors, some two received rows have **at least $n+2$ distinct MCA-bad scalars**. Since $(n+2)2^{128}>p$, this gives the operational upper bound $\delta^*\le a/n=1/3-1/(3n)$. The previous `IncidenceFullScaleCores.firstPrime_fullScale_upper` gives $(a+1)/n$. This argument determines the bad side at $a$. The good side at $a-1$ remains open.

## Three vector polynomials

Write $n=6b+4$, so $k=3b+2$ and $a=2b+1$. Number three heads cyclically. Fix their three consecutive pairs $(0,1),(1,2),(2,0)$ and choose disjoint pairs of roots $Y_i$ with exponent sets $(0,1),(3,6),(10,15)$ in this order. Let $L_i=\prod_{y\in Y_i}(X-y)$ and write $M$ for the matrix of their coefficients in increasing order. If $c_i$ is column $i$ of $\operatorname{adj}(M)$, define

$$S_i(X)=c_{i,1}-Xc_{i,0},\qquad T_i(X)=c_{i,2}-Xc_{i,1}.$$

Writing $L=M(1,X,X^2)^t$ shows $\sum_i L_i S_i=\sum_i L_i T_i=0$. Set $D_i=L_i(S_i,T_i)$. Their sum vanishes and their degrees are at most three. Set $V_0=0$, $V_1=D_0$, $V_2=D_0+D_1$, so $V_{i+1}-V_i=D_i$ cyclically. At $y\in Y_i$ the two heads at the ends of edge $i$ coincide. Their difference from the other head has projective direction $[S_j(y):T_j(y)]$ for either $j\ne i$.

Define $f_i=S_i/T_i$. The finite certificate checks that $M$ and the three maps $f_i$ are invertible, that every $f_j^{-1}f_i$ for $i<j$ has four nonzero matrix entries, and that the six directions at the twelve pair-core incidences are finite and distinct across their six coordinates. These checks use arithmetic modulo the displayed prime and its actual generator. The supplied probe reproduces them in milliseconds.

## A supply of ordinary coordinates

For a fractional linear $R=P/Q$ with invertible matrix and four nonzero entries over $\mathbb F_p$, let $U(R)=\{x\in H:R(x)\in H\}$. The following explicit bound suffices:

$$ |U(R)|\le 66060289. $$

Use $A=4096$, $B=C=64$, $d=2048$. Consider the $ABC$ rational functions

$$X^{h+ni}R(X)^{nj},\quad 0\le h<A,\quad 0\le i<B,\quad 0\le j<C.$$

They are linearly independent. Indeed, group a hypothetical relation as $\sum_j Q_j(X)R(X)^{nj}=0$ and remove its least nonzero power of $R^n$. At the finite nonzero root $z$ of $P$, $Q(z)\ne0$. Thus the lowest nonzero coefficient polynomial $Q_j$ has a root of multiplicity at least $n$ at $z$. It has at most $AB\le n$ monomials, with distinct exponents below $p$. A nonzero $s$-term polynomial with such exponents has multiplicity less than $s$ at a nonzero point. Applying the Euler operator $X\,d/dX$ successively $0,\ldots,s-1$ times gives a Vandermonde system on the distinct exponents if the multiplicity were at least $s$. This proves independence. The sparse-polynomial lemma is also in `ArkLib/ToMathlib/MonomialShiftDivisibility.lean`.

Choose a linear combination $F$ and use the differential operator $\mathcal D=XPQ\,d/dX$. The $r$-th iterate on each monomial above is that monomial times a polynomial of degree at most $2r$. For one differentiation step the logarithmic factor is

$$(h+ni)PQ+njX(P'Q-PQ'),$$

of degree at most two, and $XPQ$ times the derivative of a polynomial raises its degree by at most two. At each $x\in U(R)$ the monomial equals $x^h$. Consequently $\mathcal D^r F$ there agrees with a polynomial of degree at most $A-1+2r$ whose coefficients are linear in the chosen weights. Requiring all these polynomials to vanish identically for $0\le r<d$ imposes at most $dA+d(d-1)<ABC$ homogeneous linear conditions. Some weights survive. Independence makes the resulting $F$ nonzero.

At a point in $U(R)$, $xP(x)Q(x)\ne0$, and derivatives of orders below $d<p$ have nonzero factorials. Successive vanishing of $F,\mathcal DF,\dots,\mathcal D^{d-1}F$ therefore forces a zero of order at least $d$. Clearing $Q^{(C-1)n}$ gives a nonzero polynomial of degree at most $A-1+(B+C-2)n$. Counting multiplicities gives the claimed integer bound. Corvaja and Zannier’s Theorem 2 gives a stronger estimate for these same functions, but the displayed dimension and degree argument suffices. [Corvaja–Zannier (2013)](https://doi.org/10.4171/jems/409)

For each $i<j$ remove both endpoints of every $f_i(x)=f_j(y)$ with $x,y\in H$, counting projective equality on the whole projective line. There are at most $|U(f_j^{-1}f_i)|$ such pairs. Also remove the six special coordinates, the at most three poles, and the at most eighteen preimages of the six special directions under the three injective maps. At least $n-6\cdot66060289-27=677380063$ ordinary coordinates remain, enough to choose three disjoint private groups $G_i$ of exactly $b=178956970$ coordinates each. All three images of each chosen coordinate are finite, have distinct values across different maps, and avoid the six special labels. Injectivity handles different coordinates under a single map.

## The received rows and their witnesses

Let $C$ consist of all coordinates outside the six special coordinates and three private groups. Then $|C|=3b-2=k-4$. Define $Z=\prod_{x\in C}(X-x)$ and the three vector heads $W_i=ZV_i$. Each component has degree at most $k-1$. Define two received rows together as $W_i$ on

$$C_i=C\ \cup\ Y_{i-1}\ \cup\ Y_i\ \cup\ G_i.$$

These prescriptions cover $H$ and agree on overlaps. Each core has size $4b+2=n-a-1\ge k$.

For each $i$ and $x\notin C_i$, the difference between the received pair and $W_i(x)$ is a nonzero signed multiple of $(S_j(x),T_j(x))$ for the edge joining $i$ to the source head at $x$. The multiple is $\pm Z(x)L_j(x)$, nonzero because the two heads are different on that edge there. At a special coordinate either source gives the same direction. In each case $T_j(x)\ne0$. Thus $\gamma=-f_j(x)$ extends agreement of the mixed codeword on $C_i$ to $C_i\cup\{x\}$, whose size is $n-a$. Joint agreement on this set is impossible. Each of the two row polynomials would coincide with the corresponding component of $W_i$ on $|C_i|\ge k$ distinct points, hence everywhere. The second row disagrees at $x$.

Each private coordinate supplies two scalar labels, given by the two distinct edges out of its source. Each special coordinate supplies one. The image exclusions above ensure that the $6b+6=n+2$ labels are all distinct. This proves the asserted event mass. At one error less, three one-fresh source cores can supply at most $3a=n-1$ slots even before accounting for duplicate labels. Settling that predecessor therefore requires a different mechanism.

## Reproduction and verification scope

`python3 -O scripts/probes/probe_rate_half_mobius_seams.py` checks the literal field arithmetic and dimension inequalities. On subgroup lengths $64,256,1024$ within the same prime field it also enumerates every coordinate, constructs both received rows and all three polynomial heads, and checks every witness core, fresh point and scalar distinction directly. Their witness counts are respectively $66,258,1026$. At length $2^{30}$ the ordinary-point count is the proved analytic bound above. The script does not enumerate the billion coordinates. The production MCA event assembly remains a written proof. The general Stepanov argument has also been checked in Lean.

`ArkLib/Research/ProximityGap/Frontier/RateHalfMobiusSeamArithmetic.lean` builds using the pinned Lean 4.35 core alone. Its two matrix and direction certificates use `propext` and `Quot.sound`. Its two numerical budget theorems use no axioms. The module checks these four finite parts of the argument.

`ArkLib/Research/ProximityGap/Frontier/MobiusStepanov.lean` proves `production_mobius_intersection` for every finite field of prime characteristic above $2^{37}$. For every $a\ne0$, $a\ne b$ and $\lambda\ne0$, it counts the actual elements $x$ with $x^n=1$ and $(\lambda(x-a)/(x-b))^n=1$. The upper bound is $66060289$. The cleared derivative, sparse nonvanishing, homogeneous kernel and multiplicity steps all occur in the proof. A fixed codomain of $d(A+2(d-1))$ conditions gives the strict production dimension gap. Pinned Lean built the module, and its three printed declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
