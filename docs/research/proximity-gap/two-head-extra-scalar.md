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

## Two cubic pencils through a common polynomial

At rate $1/16$, every smooth production domain admits $2(e+1)+2$ bad labels on one received pair throughout **654,311,425 through 671,088,639 errors**, when the field exceeds $\binom{2(e+1)+1}{2}$. Thus all **16,777,215 odd budgets from 1,308,622,853 through 1,342,177,281** fail by $\lfloor B/2\rfloor-1$ in every positive width. This extends the four-fiber result above by 5,592,405 odd budgets.

Normalize the smooth coset by its representative. Set $s=k/4$, $r=s-2$ and $T=X^s$. Its image has order 64, each image point has $s$ preimages, and the image contains an element $w$ of order 16. For a triple $J$ let $P_J(T)=\prod_{a\in J}(T-w^a)$. Use the following exponent sets.

| Triple | Exponents | Vanishing polynomial up to nonzero scalar |
| --- | --- | --- |
| $A$ | $0,1,8$ | $W$ |
| $B$ | $2,9,10$ | $Q$ |
| $C$ | $3,5,7$ | $W-Q$ |
| $D$ | $6,9,14$ | $V$ |
| $E$ | $7,11,13$ | $W-V$ |

Take $W=P_A$. For either $(J,K)=(B,C)$ or $(D,E)$, put $u=P_A(0)-P_K(0)$ and $v=P_J(0)-P_K(0)$. The coefficient identity $v(P_A-P_K)=u(P_J-P_K)$ holds in $\mathbb Z[w]/(w^8+1)[T]$. For both pairs the absolute norms of $u,v,v-u$ are $4,4,16$, respectively. Consequently $(u/v)P_J$ and its difference from $W$ have exactly the indicated roots over every field admitting a primitive sixteenth root. Use $(u/v)P_B$ for $Q$ and $(u/v)P_D$ for $V$, with their respective coefficients. Their zero sets differ, so $Q-V$ is nonzero. Two of its roots are $w^7,w^9$, leaving at most one further root. The finite checker multiplies the integer coefficient vectors and checks both identities and all six norms. Lean also proves the factorizations of $W-V$ and $Q-V$, and verifies their leading coefficients are nonzero at order 16. [Lean cubic identities](../../../ArkLib/Research/ProximityGap/Frontier/TwoCubicExtraSeed.lean) · [Exact identities and finite reconstruction](../../../scripts/probes/probe_two_projective_extra_labels.py)

Pull back the three cubics along $T$. Reserve their $A$ fibers for the intersection of the two cores. Reserve the $B\cup D$ fibers for the first private core and the $C\cup E$ fibers for the second. These two five-element unions and $A$ are disjoint. Place all as-yet-unassigned roots of $Q-V$ in the first private core, costing at most $s$ sites. At least $50s$ of the $64s$ sites remain available. Choose $r$ of them as common locator roots and multiply $W,Q,V$ by this locator. The resulting degrees are $k-2$.

Fill each core to $t-1$ sites, where $t=n-e$, keeping their intersection exactly the $r+3s$ prescribed sites. This is possible because $r+9s\le t-1$ and $2(t-1)-r-3s\le n$ throughout the interval. Write $O$ for the complement. Its size is $n-2t+2+r+3s\ge k$. On the first core use the normalized pair $(0,0)$, on the second use $(W,W)$, and on $O$ use $(Q,V)$. For the received pair multiply the second normalized row by $X+\theta$.

On $O$, all of $W,Q,V,Q-W,V-W,Q-V$ are nonzero. The two exterior slopes $V/Q$ and $(V-W)/(Q-W)$ differ since $W(V-Q)\ne 0$. Multiplying these slopes by $x+\theta$, and using slope one at private core sites, yields exactly the separation argument above. On every private site $x+\theta\ne0$, since it contributes a fresh label for the opposite head. This supplies $2(e+1)$ distinct finite nonzero labels, with support sizes $t$ and unique head interpolation on their respective cores.

At zero the first row agrees with $Q$ on $O$, the locator roots and the $B,C$ fibers. At infinity the second row agrees with $(X+\theta)V$ on $O$, the locator roots and the $D,E$ fibers. Each support has size
\[
  |O|+r+6s=n-2t+2+2r+9s.
\]
It reaches $t$ exactly when $3t\le n+11k/4-2$. Joint interpolation on $O$ pins the polynomial pair to $(Q,(X+\theta)V)$. On the $w^3$ fiber of $C\setminus E$, the second row differs from that pair. On the $w^{11}$ fiber of $E\setminus C$, the first row differs. The same invertible row change as above preserves all the witnesses and places them in one affine chart. Lean verifies the eight exceptional quotient classes, the partition of the remaining sites, the simultaneous mass and the odd-budget threshold at every positive width. [Power-fiber geometry](../../../ArkLib/Research/ProximityGap/Frontier/TwoCubicExtraFibers.lean) · [Field and threshold endpoints](../../../ArkLib/Research/ProximityGap/Frontier/TwoCubicExtraCoset.lean) At $n=256,k=16$ the checker explicitly reconstructs 318 finite bad labels at 157 errors, and 320 and 322 at the next two errors. [Lean normalized-row witness theorem](../../../ArkLib/Research/ProximityGap/Frontier/TwoProjectiveExtraWitness.lean) · [Replay](../../../scripts/probes/probe_two_projective_extra_labels.py)

### Obstruction for four completely split fibers in a single cubic pencil

On the 64th roots of unity over $\mathbb C$ or in any splitting prime field of characteristic greater than $24^{32}$, a cubic pencil has at most three pairwise disjoint, completely split three-point fibers. In particular this obstruction applies to both named prime fields. The two pencils above bypass it.

Represent a root triple by $(a,b,c)$, its elementary symmetric functions. Its monic cubic has coefficient vector $(1,-a,b,-c)$. Four such cubics belong to a pencil precisely when the four triples are collinear in affine three-space. Over $\mathbb F_{65537}$, fix the first root triple up to rotation and inversion, which act projectively on cubics by rescaling the variable and reversing coefficients. There are 341 representatives. From each representative the checker computes the normalized directions through the other $\binom{61}{3}$ triples disjoint from it. None of the 12,272,590 comparisons gives three other triples in the same direction. A pencil through two disjoint triples has no common root, so any additional distinct fibers on that line are also disjoint. The exact maximum is three. [Census and replay at each named prime](../../../scripts/probes/probe_mu64_cubic_pencil_fibers.py)

For the transfer, put $L=\mathbb Q(\zeta_{64})$ and reduce at the primitive root used in the screen. For any four disjoint triples, some two-by-two minor of the three difference vectors is nonzero after reduction and therefore in $L$. If the products $c$ differ, they also differ after reduction, as they are powers of $\zeta_{64}$. At least one nonzero minor can then be chosen using the product column. Its absolute value in every complex embedding is at most $2\cdot6\cdot2=24$, since each sum or pair-sum difference has absolute value at most six. Its nonzero integer norm is at most $24^{32}$.

If all four products equal a common $c$, every pair sum equals $c\overline a$. Take a nonzero minor of the other two columns. Dividing it by $ic$ gives a real algebraic integer, because the determinant of the two difference vectors has the form $c(u\overline v-v\overline u)$. Its absolute value under every embedding is at most 72. Its nonzero absolute norm from the degree-sixteen real subfield is at most $72^{16}<24^{32}$. In both cases no prime larger than $24^{32}$ can annihilate the selected minor. The argument also excludes any complex layout by reduction at 65537.
