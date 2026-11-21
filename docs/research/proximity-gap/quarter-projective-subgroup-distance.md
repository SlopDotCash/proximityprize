# How far the three directions must be from projective copies of the subgroup

Let $H=\mu_n$, $n=2^{30}$, $d=n/4-1$ in the named second prime field. Use the geometric direction line, its involution $J$, and the three degree-$m_i$ maps $z_i$ from a hypothesized four-head overrun at $n/2$ errors. For each pair $i,j$, there are $s=m_i+m_j$ double sites for each of the two relations $z_j=z_i$, $z_j=Jz_i$. The actual fresh directions are the nonfixed orbit $[z_i]=\{z_i,Jz_i\}$. The full set of $4d$ double sites loses at most one value under the orbit map. [Reconstruction](quarter-three-slope-reconstruction.md)

Call any $S=M(H)$, with $M$ a Möbius transformation over the algebraic closure, a projective copy of $H$. **Two different copies intersect in at most $C=4993531$ points.** Indeed the transition between the two copies gives a Möbius graph in $H\times H$. A non-toric graph has the stated bound by Corvaja–Zannier. For a toric graph $u\mapsto cu^{\pm1}$ the transformed subgroup is a multiplicative coset, so any intersection makes the two copies equal. [Graph bound and integer cutoff](quarter-slope-power-barrier.md#two-fractional-linear-transforms-of-powers)

Choose any three copies $S_i$ independently and set $L_i=\#\{x\in H:z_i(x)\notin S_i\}$. Then
\[
 L_1+L_2+L_3\ge 534374144.
\]
Some single map therefore misses **every** projective copy on at least **178124715** evaluation sites. To see this last quantifier, choose an individually minimizing copy for each map.

Call a double site good when both of its participating maps land in their designated copies. The other $4d-\#\mathrm{good}$ sites contribute at least once to the sum of the three $L_i$. Partition the copies by the equivalence $S\sim J(S)$.

- If the three classes are distinct, each signed locus has its good values in the intersection of two distinct copies. Across the six loci this accounts for at most $6C+1$ good sites, including the possible repeated orbit.
- If two copies belong to the same invariant class $S=J(S)$, they both equal $S$. Every good site involves one of them. A projective involution has at most two fixed points, so $S$ has at most $n/2+1$ orbits. At most $n/2+2$ sites are good.
- If exactly two copies share a noninvariant class and the third is outside it, the four loci involving the outsider have at most $4C$ distinct good orbits. For the pair in the same class, one sign aligns the copies and contributes at most $s\le d$ orbits. For the other sign each good orbit has both elements in $S\cap J(S)$, so this contributes at most $\lfloor C/2\rfloor$ orbits. The total number of good sites is at most $d+5C+1$.
- If all three copies belong to one noninvariant class, one sign per pair aligns the copies. These three loci contain $\sum_{i<j}(m_i+m_j)=2d$ sites. Every other good site has its entire orbit in the **same** set $S\cap J(S)$. Hence there are at most $2d+\lfloor C/2\rfloor+1$ good sites.

The claimed bounds follow in all four cases. [Lean count](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

There is also a sharp form of the earlier pair test: if the full images of two maps lie in any two projective copies of $H$, their degree sum is at most $C$. Otherwise one signed locus has $s>C$ distinct orbits because the two disjoint loci cannot both contain an internal repeat. After applying $J$ to the second copy if necessary, the intersecting copies must therefore agree, say in $S$. On the other locus at least $s-1$ distinct **two-element** orbits lie in $S\cap J(S)$, which forces $J(S)=S$. At least one participating degree $m$ is at least three. The lower bound $n/2+2m-3$ for that map's orbit image contradicts the upper bound $n/2+1$ on $S$. This argument imposes no restriction on the rational formulas of the two maps. [Individual image bound](quarter-slope-power-barrier.md#each-individual-map-has-a-large-image-on-the-prescribed-domain)

## Bounds on one map equivalent to a power

Suppose $z_i=M(N(X)^a)$ where $M,N$ are arbitrary invertible fractional linear maps. If $a$ is the largest degree, each companion $R$ of degree $b$ has **$b\ge69148$**. If $N(X)=X$, each companion has **$b\ge4436951$**, and every unshifted power degree, largest or otherwise, satisfies **$a\le201326591$**.

For the first bound we may take $a>b$, since $a\ge d/3=89478485$. Put $V=M^{-1}R$ and $G=N^a/V$. Common zero or pole sites of $N^a,V$ number $h\le2$. They belong to the full simple positive coincidence divisor. Removing their common factors in homogeneous coordinates shows $\deg G\le a+b-h$, and at the other $a+b-h$ positive sites $G=1$. If $G$ were multiplicatively dependent with $X$, its divisor would be supported at $0,\infty$, making $G=cX^r$. A zero or pole of $N$ elsewhere has order $a>b$ in $N^a$ and cannot be canceled by $V$. Thus $N$ would also be toric and $V$ a scaled monomial, making the two map images lie in projective copies of $H$ and contradicting the pair test.

Apply Corvaja–Zannier's Theorem 2 on the rational line to $X^n,G$. Both differentials are nonzero since the degrees are positive and below $p$. The zero and pole set of the two functions has at most $2+2+2b$ elements. With $\chi\le 2b+2$ and $12n(a+b)/p<1$, the theorem and the coincidence count give
\[
 (a+b-2)^2\le (a+b-h)^2\le108n(b+1).
\]
At $a\ge89478485$ this forces $b\ge69148$. With $N=X$ there are no common zero or pole sites, and the same argument gives $(a+b)^2\le108nb$. [Corvaja and Zannier, Theorem 2](https://doi.org/10.4171/JEMS/409) · [Checked numerical implications](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

For $N=X$ there is a stronger elementary bound. At all $a+b$ positive sites $V(X)=X^a$ is finite and nonzero. For each positive integer $k$ and integer $l$, the functions $V^k$ and $X^{ka-ln}$ agree at those sites. If they agree identically, the divisor of $V$ is supported at $0,\infty$, giving the excluded pair of projective subgroup images whenever $a+b>C$. Otherwise their projective coincidence divisor has degree at most
\[
 a+b\le kb+|ka-ln|.
\]
When $a$ is largest put $k=\lfloor n/a\rfloor$ and $r=n-ka$. Then $4\le k\le12$, $0\le r<a$. Applying the two tests $k,k+1$ with $l=1$ gives $a-r\le(k-1)b$ and $r\le kb$. The nine integer cases imply $b\ge4436951$. For the degree ceiling, apply the fifth-power test with $l=1$ to both companions $b,c$. Using $a+b+c=d$, its two inequalities imply $a\le201326591$ in each sign of $5a-n$. For $a\le C$ the ceiling already holds. [Lean integer case proof](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSlopePowerBarrier.lean)

The numerical distance bound applies to arbitrary rational slopes. It leaves open the existence of maps meeting these distances and the full signed coincidence equations.
