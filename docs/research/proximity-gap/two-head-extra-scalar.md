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
