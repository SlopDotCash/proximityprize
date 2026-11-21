# Restricted images of the three quarter-rate direction maps

Let $H=\mu_n$ with $n=2^{30}$ in the named second prime field, $d=n/4-1$. Suppose four genuine heads produce more than $2n$ bad scalars at $n/2$ errors. Use the three direction maps $z_i$ of positive degrees $m_i$ with $\sum m_i=d$. In eigen-coordinates their common involution is $J(z)=-z$, also in the nonsplit case after the quadratic extension. The map $x\mapsto[z_i(x)]$ takes values in $\mathbb P^1/J$. All counts below work over the algebraic closure and permit arbitrary projective changes of the individual directions. [Reconstruction and orbit criterion](quarter-three-slope-reconstruction.md)

## Each individual map has a large image on the prescribed domain

The two signed coincidence loci of $z_i$ and $z_j$ each have $m_i+m_j$ distinct sites. The four loci involving $z_i$ therefore contain $2(d+m_i)$ distinct sites. On these sites $[z_i(x)]$ is the actual fresh-direction orbit. The full set of double sites loses at most one value under the orbit map, so the same holds on every subset. Consequently
\[
 \#\{[z_i(x)]:x\in H\}\ \ge\ 2(d+m_i)-1=n/2+2m_i-3.
\]
In particular at least one map has at least $715827879$ distinct projective direction orbits. If $m_i\ge2$, every fixed-point-free involution of $H$ has some pair on which $[z_i]$ takes different values. This excludes a single map factoring through $X^2$, regardless of its companions. It also excludes $z_i(-X)=J z_i(X)$ for $m_i\ge2$. The restriction-of-image estimate and its half-length consequence are formalized in Lean. [Finite-set proof](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

## Two fractional linear transforms of powers

Suppose two maps have the form $z_i=M_i(X^a)$ and $z_j=M_j(X^b)$, with $M_i,M_j$ arbitrary independent Möbius transformations over the algebraic closure. Then
\[
 a+b\le 4993531 .
\]
In particular the three maps cannot all have this form. The result allows different powers, independently chosen numerator and denominator coefficients, and inversion absorbed into either $M$.

**Proof.** Positive even exponents are impossible by the individual image bound. Thus $a,b$ are odd, and both power maps permute $H$. Put $s=a+b$. For $L=1,J$, the $s$ distinct sites satisfying $z_j=Lz_i$ give $s$ distinct points of $H\times H$ on the graph of $N_L=M_j^{-1} L M_i$, with coordinates $(x^a,x^b)$. This includes coincidences at poles in the original target because the graph itself is read projectively before restricting its coordinates to the torus.

Unless $N_L(u)=cu$ or $c/u$, that graph in the torus is absolutely irreducible and its coordinates are multiplicatively independent modulo constants. Indeed any relation between the two coordinates on a Möbius graph requires its zero and pole to be $0,\infty$. Its bidegree is $(1,1)$, and deleting the zeros and poles from its rational normalization removes at most four points. Its Euler characteristic in the positive-sign convention is at most two. Corvaja–Zannier bound the graph intersection by $\max(3(4n^2)^{1/3},12n^2/p)$. The second term is below one. The first is strictly between 4993531 and 4993532; Lean verifies this integer cutoff. [Corvaja and Zannier, Corollary 2](https://doi.org/10.4171/JEMS/409) · [Checked integer comparison](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

If $s\ge4993532$, both graphs must therefore be torus translates. A scaling graph would give $X^{b-a}=c$ on $s$ sites. For unequal exponents this has at most $|b-a|<s$ solutions. For equal exponents the coincidence is empty or identically true, while the locus must have exactly $0<s<n$ sites. Hence both $N_1$ and $N_J$ are inversions. Their quotient $N_J N_1^{-1}=M_j^{-1}JM_j$ is a nonidentity scaling of order two, necessarily $u\mapsto-u$. The quotient $N_1^{-1}N_J$ gives the same conclusion for $M_i$. Thus $z_i(-x)=Jz_i(x)$ and $z_j(-x)=Jz_j(x)$. At least one degree is at least two, contradicting its individual image bound. Finally, the largest of three degrees summing to $268435455$ is at least $89478485$, already exceeding the pair cutoff.

## One power slope with an arbitrary rational companion

Suppose $z_i=M(X^a)$ with $a\ge4993532$ and another map is $R(X)$ of degree $b$. Then
\[
 (a+b)^3\le108 b^2 n^2.
\]
In particular, if the largest degree belongs to a power slope, **both** remaining degrees are at least $76$.

To see this, the positive coincidence sites $(x,x^a)$ lie on the graph $v=M^{-1}R(u)$. If it were a torus translate, the rational graph would have the form $v=cu^{\pm b}$, making $R$ another transformed power and violating the preceding pair bound. The non-toric graph has bidegrees $b,1$ and on its rational normalization at most $2+2b$ punctures, so its positive-sign Euler characteristic is at most $2b$. There are $a+b$ distinct marked points on it. Corvaja–Zannier give the asserted cube bound since $12bn^2<p$. At $a\ge89478485$ the cube bound with $b\le75$ fails by direct integer comparison. [Source inequality](https://doi.org/10.4171/JEMS/409) · [Checked degree bound](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

The unrestricted question still asks whether three rational maps can realize the six prescribed split divisors and the required orbit count on $H$.
