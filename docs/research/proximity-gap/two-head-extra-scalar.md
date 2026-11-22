# Two full secants and an extra bad scalar at rate one sixteenth

Let $n=2^{30}$, $k=n/16$, and let the evaluation domain be a multiplicative coset of order $n$ in a finite field $F$. For every integer $654311425\le e\le671088639$, put $t=n-e$ and $N=2(e+1)$. If $|F|>\binom{N+1}{2}$, **one received pair has at least $N+1$ distinct bad scalar labels at $e$ errors**. The construction is uniform in the field and the choice of coset representative. The Lean theorems `smooth_mass` and `even_ceiling` prove the probability and threshold bounds using the simultaneous witness theorem `witnesses`. [Production specialization](../../../ArkLib/Research/ProximityGap/Frontier/TwoHeadExtraCoset.lean) · [Bad-label witnesses](../../../ArkLib/Research/ProximityGap/Frontier/TwoHeadExtraWitness.lean)

For every even budget $B$ from **1308622852** through **1342177280**, put $e=B/2-1$. Its field size satisfies the displayed inequality since $|F|\ge2^{128}B$. The first MCA failure at every positive interleaving width is therefore at most $B/2-1$. The two-head attack alone first exceeds the even budget at $B/2$. Supplied smooth domains of this length admit the required multiplicative coset presentation. [Coset equivalence](../../../ArkLib/Research/ProximityGap/Frontier/SmoothDomainMcaEquivalence.lean) · [Positive-width invariance](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)

## A split pencil on the supplied domain

Write $s=k/4$, $D=3s$, and $r=s-2$. The image of the normalized coset under the $s$th-power map has order 64. Take its element $w$ of order 16. On the order-64 quotient the three polynomials
\[
 0,\quad (T-1)(T-w)(T-w^8),\quad
 w^2(T-w^2)(T-w^9)(T-w^{10})
\]
have three disjoint pairwise coincidence sets of size three. The equality of the two nonzero polynomials occurs at $w^3,w^5,w^7$. The identity holds in all characteristics admitting the stated roots. Pulling back by the normalized $s$th-power map gives three disjoint sets $J_{01},J_{02},J_{12}$ of $D$ coordinates each. [Polynomial identity and coset specialization in Lean](../../../ArkLib/Research/ProximityGap/Frontier/SmoothCosetCubicSeed.lean)

Choose $r$ further sites $R$ outside the three sets. Multiply the two nonzero pullbacks by the monic locator of $R$ and call the resulting polynomials $W,Q$, respectively. Both have degree $r+D=k-2$. On the domain the zeros of $W,Q,Q-W$ are exactly $R\cup J_{01}$, $R\cup J_{02}$ and $R\cup J_{12}$, respectively.

## The received rows

Choose two $(t-1)$-site sets $A,B$ with
\[
 A\cap B=R\cup J_{01},\qquad J_{02}\subseteq A\setminus B,
 \qquad J_{12}\subseteq B\setminus A.
\]
Start with the prescribed sites and fill the two private parts disjointly. This is possible because $r+2D\le t-1$ and $2(t-1)-(r+D)\le n$. Put $O=(A\cup B)^c$. Then $|O|=n-2t+2+r+D\ge k$. Define a word $b$ by $b=0$ on $A$, $b=W$ on $B$ and $b=Q$ on $O$. Its prescriptions agree on $A\cap B$. For a parameter $\theta\in F$, receive
\[
 u_0(x)=b(x),\qquad u_1(x)=x b(x)+\theta\,\mathbf1_O(x).
\]
The two pairs of polynomials $(0,0)$ and $(W,XW)$ have degree below $k$ and agree with the two rows throughout $A$ and $B$, respectively.

Every site outside either core supplies a new scalar for that core. On $B\setminus A$ the first core's label is $-1/x$, and on $A\setminus B$ the second core's label is $-1/x$. On $O$ their labels are $-1/\alpha_0$ and $-1/\alpha_1$ with
\[
 \alpha_0=x+\theta/Q(x),\qquad \alpha_1=x+\theta/(Q(x)-W(x)).
\]
The denominators in the coefficients of $\theta$ are nonzero on $O$. There are $N$ affine functions of $\theta$ in these prescriptions, one on each opposite private core site and two on each site of $O$. At distinct sites their constant terms are distinct. At each site of $O$ their slopes are distinct because $W(x)\ne0$. Adjoin the identically zero function, distinct from them all since every coset site is nonzero. Each pair collides at at most one parameter. The field size allows a $\theta$ making all $N+1$ values distinct. This choice also has $\theta\ne0$, since the two values at each site of $O$ coincide at zero.

For each finite label thus obtained, the relevant projected head agrees on its full core plus the fresh site, a set of $t$ coordinates. Joint interpolation there would force both row polynomials to equal that head, by agreement at the $t-1\ge k$ core sites. At the fresh site the first received row differs from the first entry of the head. Hence every one of these $N$ distinct nonzero labels is bad in the fixed-support MCA definition.

## The extra scalar

At scalar zero the projected witness is $Q$. Its agreement set includes $O\cup R\cup J_{02}\cup J_{12}$, of size
\[
  |O|+r+2D=n-2t+2+2r+3D.
\]
This is at least $t$ precisely when $3t\le n+2r+3D+2=n+11k/4-2$. The largest integer $t$ allowed is $419430399$, giving the first stated error $654311425$.

If a polynomial of degree below $k$ agreed with the second received row on this set, its values on $O$ would force it to be $XQ+\theta$, whose degree is at most $k-1$. At every coordinate of $J_{02}$ the actual second row is zero and $XQ+\theta=\theta\ne0$. Thus zero is another bad label. The same received rows realize all $2(e+1)+1$ labels simultaneously.

## Two extra directions from four power fibers

Let $659903830\le e\le671088639$, $N=2(e+1)$, and $|F|>\binom{N+1}{2}$. There is a single received pair with **$N+2$ finite bad scalar labels** on every smooth production domain. In particular, all **11,184,810 odd budgets** from 1,319,807,663 through 1,342,177,281 fail by $\lfloor B/2\rfloor-1$ errors at every positive width.

Normalize the coset to a subgroup and let $s=k/2$, $r=s-2$. The map $T=X^s$ on this subgroup has 32 fibers of size $s$. Choose distinct image values $a,b,c,d$, with fibers $J_a,J_b,J_c,J_d$. Put $\lambda=(c-a)/(c-b)$ and $\eta=(d-a)/(\lambda(d-b))$. Both constants are nonzero and $\eta\ne1$ since $u\mapsto(u-a)/(u-b)$ is injective away from $b$. Choose $r$ sites $R$ outside these four fibers and let $H$ be their locator. Set
\[
 W=H(T-a),\qquad Q=\lambda H(T-b).
\]
Outside $R$, the four equations $W=0$, $Q=0$, $Q=W$, $\eta Q=W$ hold exactly on $J_a,J_b,J_c,J_d$, respectively. The polynomials have degree $k-2$.

Take two cores $A,B$ of size $t-1$, with intersection $R\cup J_a$, with $J_b\subset A\setminus B$ and $J_c\cup J_d\subset B\setminus A$. Fill the two cores disjointly outside those prescribed sites. There is room because $r+3s\le t-1$ and $2(t-1)-r-s\le n$. On $A,B,O=(A\cup B)^c$ prescribe $(u,v)$ respectively as
\[
  (0,0),\qquad (W,(X+\theta)W),\qquad(Q,\eta(X+\theta)Q).
\]
Here $X$ denotes the normalized evaluation coordinate. Multiplication by the known coset representative preserves the polynomial degree cap under this change of coordinates.

Each fresh scalar for a head has reciprocal parameter $\alpha$ such that its label is $-1/\alpha$. On an opposite private core $\alpha=x+\theta$. On $O$ the two parameters are
\[
 \eta(x+\theta),\qquad \frac{\eta Q(x)-W(x)}{Q(x)-W(x)}(x+\theta).
\]
All slopes multiplying $x+\theta$ are nonzero. The two slopes at any one exterior site differ since $(\eta-1)W(x)\ne0$. At distinct sites nonzero slopes yield distinct affine functions of $\theta$, by comparing their linear and constant coefficients. Pairwise separation of these $N$ functions and the constant zero is possible by the field size bound. The $N$ resulting finite nonzero labels are bad by the same core-plus-fresh-site argument as above.

The first row agrees with $Q$ on $S_0=O\cup R\cup J_b\cup J_c$. The second agrees with $P=\eta(X+\theta)Q$ on $S_\infty=O\cup R\cup J_b\cup J_d$. Both supports have cardinality $n-2t+2+2r+3s\ge t$ exactly when $3t\le n+2k+k/2-2$, giving the stated lower limit on $e$. The common exterior has cardinality $n-2t+k\ge k$. Thus any joint explanation must use the pair $(Q,P)$. On $J_c$, the second row differs from $P$ because $Q=W\ne0$, $\eta\ne1$, and the fresh parameter $x+\theta$ on this private core is nonzero. On $J_d$, the first row $W=\eta Q$ differs from $Q$. This witnesses both additional projective directions.

To exhibit all these directions in the finite scalar parameter, choose $h\in F$ outside the $N+1$ existing finite directions. Replace $(u,v)$ by $(v,u+h v)$. At parameter zero this projects to the old direction at infinity. For any of the old finite labels $z$, parameter $1/(z-h)$ gives a nonzero multiple of $u+zv$. The invertible change of rows preserves joint interpolability on each fixed support, in both directions. This gives $N+2$ distinct finite bad labels for one pair. For odd $B=2e+3$ the field-size hypothesis follows from $|F|\ge B2^{128}$, and $N+2=B+1$.

The finite reconstruction at $n=256$, $k=16$ over $\mathbb F_{65537}$ verifies 320 labels at $e=158$ and 322 at $e=159$, including both extra supports before the row change. The Lean proof chooses the four quotient sites $1,-1,w,-w$, where $w$ has order four, and uses $W=H(T-1)$ and $Q=wH(T+1)$ with $\eta=-1$. It establishes both the probability lower bound and the odd-budget threshold inequality. [Four quotient fibers](../../../ArkLib/Research/ProximityGap/Frontier/TwoProjectiveExtraFibers.lean) · [Operational threshold](../../../ArkLib/Research/ProximityGap/Frontier/TwoProjectiveExtraCoset.lean) · [Reproduction](../../../scripts/probes/probe_two_projective_extra_labels.py)
