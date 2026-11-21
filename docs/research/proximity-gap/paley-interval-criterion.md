# The short interval obstruction in prime-field Paley discrepancy

Fix a family of odd primes. Write $\chi(0)=0$ and $S(A,B)=\sum_{a\in A,b\in B}\chi(a-b)$. The following three statements are equivalent on that same family. In each statement, for every $\epsilon>0$ there must exist $\delta>0$ and $C$ so that the bound holds for all sufficiently large primes in the family.

1. Every pair of unit-step intervals of lengths $H,K\ge p^\epsilon$ satisfies $|S(A,B)|\le C HKp^{-\delta}$.
2. Every translated interval of length $H\ge p^\epsilon$ satisfies $|\sum_{i=0}^{H-1}\chi(s+i)|\le C H p^{-\delta}$.
3. For every arithmetic progression $A$ of length $H\ge p^\epsilon$ and nonzero step, and every $B\subseteq\mathbb F_p$, one has $|S(A,B)|\le C H |B| p^{-\delta}$. There is no lower bound on $|B|$.

The lengths are at most $p$ and intervals can wrap around zero. The constants and exponents may change from one statement to another. The fully quantified equivalences and the nonresidue consequence below are checked in Lean. [Formalization](../../../ArkLib/Research/ProximityGap/Frontier/PaleyIntervalCriterion.lean)

## The exact finite comparison

Put $T(s,H)=\sum_{i=0}^{H-1}\chi(s+i)$ and $R(s;H,K)=\sum_{j=0}^{K-1}T(s+j,H)$. This is the difference sum on the intervals $\{s,\ldots,s+H-1\}$ and $\{0,-1,\ldots,-(K-1)\}$. Every pair of ordinary intervals of these lengths has this form after simultaneous translation and reversing the order of the second interval. Since $T(s+1,H)-T(s,H)=\chi(s+H)-\chi(s)$, for all $H,K\ge0$ we have
$$
 |R(s;H,K)-KT(s,H)|\le \sum_{j=0}^{K-1}2j=K(K-1).
$$
Thus for $K\ge1$, a bound $|R|\le \rho HK$ yields $|T(s,H)|\le \rho H+K-1$. For $H\ge p^\epsilon$ take $K=\lceil p^{\epsilon/2}\rceil$. A rectangle saving $C p^{-\delta}$ at scale $\epsilon/2$ gives an interval saving $(C+1)p^{-\min(\delta,\epsilon/2)}$ relative to $H$.

For the converse, write $A=\{s+di:0\le i<H\}$ with $d\ne0$. The contribution at each $b$ equals $\chi(d)T((s-b)/d,H)$. Summing the uniform interval estimate over $B$ gives statement 3 directly. In particular, Burgess's theorem already gives a power saving for every such partner if the progression has length at least $p^{1/4+\kappa}$ for fixed $\kappa>0$. Its application here uses the published character-sum bound. [Burgess, *On Character Sums and L-Series II*](https://doi.org/10.1112/plms/s3-13.1.524) · [Uniform prime-modulus estimate, Theorem 1.1](https://arxiv.org/abs/1711.10582)

## Least quadratic nonresidue

If $H+K-1<p$ and $R(1;H,K)<HK$, then some positive $n\le H+K-1$ has $\chi(n)=-1$. Otherwise every difference in this rectangle has character $+1$. In particular any strict improvement over the trivial bound for this single $m$-by-$m$ rectangle gives a quadratic nonresidue at most $2m-1$, when $2m-1<p$.

Consequently any of the three all-scale statements implies that for every $\epsilon>0$ the least quadratic nonresidue is at most $p^\epsilon$ for all sufficiently large primes in the chosen family. Equivalently, use the second statement on the interval beginning at 1, with length $\lceil p^{\min(\epsilon/2,1/2)}\rceil$. For the family of all odd primes this is Vinogradov's least quadratic nonresidue conjecture. A hypothesis restricted to $p\equiv1\pmod4$ yields the conclusion on that class. The converse from the least nonresidue alone is not part of the equivalence. [Tao, *The Elliott–Halberstam conjecture implies the Vinogradov least quadratic nonresidue conjecture*](https://arxiv.org/abs/1410.7073)
