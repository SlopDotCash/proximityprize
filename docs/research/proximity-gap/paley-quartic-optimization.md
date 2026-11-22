# An unconstrained quartic optimization equivalent to Paley discrepancy

For a subset $X$ of the prime field, write $B(X)=\binom{|X|}{4}$ and let $N(X)$ count its singular four-site principal Paley minors over $\mathbb F_3$. Both are multilinear quartics in the Boolean indicators $x_v$. Each monomial chooses four distinct field points and has coefficient either zero or one. Write $e=\chi_p(-1)$ and define
$$
 U_p(h)=\max_{x\in\{0,1\}^{p}}
      \left(e\left(N(X)-\tfrac14B(X)\right)-h B(X)\right).
$$
The unrestricted quadratic Paley discrepancy conjecture is equivalent to the following bound on this optimization problem with no cardinality constraint. For every fixed $0<\epsilon<1$ there is $\eta>0$ such that $U_p(p^{-\eta})=O_\epsilon(p^{4\epsilon})$ over all sufficiently large odd primes.

Indeed, discrepancy bounds the absolute singular-density deviation by $O(p^{-\eta})$ on all sets of size at least $p^\epsilon$. One obtains the bound uniformly in larger sizes by averaging the four-subset statistic over subsets of size $\lceil p^\epsilon\rceil$. Decrease $\eta$ to absorb the constant. Smaller sets contribute at most $O(p^{4\epsilon})$ to the objective. Conversely fix $0<\alpha<1$ and use the proposed optimization bound at $\epsilon=\alpha/2$. For $|X|\ge p^\alpha$, division by $B(X)$ bounds the signed density deviation by $p^{-\eta}+O(p^{-2\alpha})$. The identity
$$
 E(X,X)=|X|(|X|-1)(2|X|-3)+32e\big(N(X)-B(X)/4\big)
$$
and $E(X,X)\ge0$ bound the opposite deviation by $O(1/|X|)$. The resulting uniform density law implies the required discrepancy for two arbitrary polynomial-size sets. [Four-site rank equivalence](paley-four-site-rank.md)

## What the ordinary degree-four relaxation returns

At primes $p\equiv1\pmod4$, the Boolean degree-four sum-of-squares relaxation of this maximization has value at least
$$
             (3/4-h)\binom{s}{4},\qquad s\ge c p^{1/3},
$$
for $0\le h\le3/4$ and large $p$. In particular its upper bound on $U_p(p^{-\eta})$ is $\Omega(p^{4/3})$, for each fixed $\eta>0$. This separates the degree of the objective from the degree needed for this particular proof method at any $\epsilon<1/3$.

Use the clique pseudoexpectation constructed by Kunisky and Yu. It is a normalized linear functional $L$ on real polynomials through degree four. It respects the Boolean relations to that degree, is nonnegative on squares of polynomials of degree at most two, vanishes on every squarefree monomial containing a nonedge, and has $s=L(S)\ge c p^{1/3}$ for $S=\sum_v x_v$. Forgetting its nonedge constraints gives a feasible point for the Boolean relaxation here. For every four-clique the Paley matrix is $J-I$ of size four, with integer determinant $-3$. Thus all four-site monomials carrying clique mass are counted by $N$, and $L(N)=L(B)$. This equality uses no assumption on the signs of the individual pseudomoments. [Kunisky and Yu, Theorem 1.2 and the moment constraints in equation (10)](https://arxiv.org/pdf/2211.02713)

In the Boolean quotient $24B=(S)_4=S(S-1)(S-2)(S-3)$. For $Q=S^2-3S+1$ one has $(S)_4=Q^2-1$. Positivity of the squares of $S-s$ and $Q-L(Q)$ gives $L(S^2)\ge s^2$ and $L(Q^2)\ge L(Q)^2$. Since $s\ge3$, it follows that $L((S)_4)\ge(s^2-3s+1)^2-1=(s)_4$. This proves the displayed relaxation bound. The Lean lemma works for any normalized functional on univariate moments with the stated square positivity. Higher-degree values of an arbitrary extension of the functional do not enter its proof. [Moment inequality and clique minor in Lean](../../../ArkLib/Research/ProximityGap/Frontier/PaleyQuarticCertificate.lean)

For a prescribed first moment $4\le k\le s$, independently retain each variable with probability $k/s$ and average the functional after setting the discarded variables to zero. This still gives a feasible pseudoexpectation, now with first moment $k$, and $L(N)=L(B)\ge\binom k4$ by the same argument. The exact-cardinality relaxation also requires contractions against all test monomials through degree three. That case uses a separate construction. [Exact-cardinality moment matrix](paley-quartic-slice.md) A design-based construction also realizes both extremes of the rank objective at every sufficiently large odd prime. [Both exact-size rank witnesses](paley-quartic-design-relaxation.md)
