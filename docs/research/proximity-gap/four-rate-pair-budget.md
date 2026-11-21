# Exact four-rate MCA thresholds on a prime-field budget interval

Let $n=2^{30}$ and let $g$ have order $n$ in $\mathbb F_p^\times$. For the Reed–Solomon code of dimension $1\le k\le n/2$ on $\langle g\rangle$, write $B=\lfloor p/2^{128}\rfloor$. If $1\le B\le181823221$, the first error count failing the $2^{-128}$ MCA target is $B$ and the last good count is $B-1$. For every positive interleaving width, the full good-radius interval is
$$
0\le\delta<B/1073741824.
$$
This includes all four prize rates for each prime and subgroup in this range. [Kernel-checked theorem](../../../ArkLib/Research/ProximityGap/Frontier/FourRatePairBudget.lean)

## Why the count is exact

For each bad scalar choose its witnessing polynomial and the full set of agreements, of size at least $t=n-e$. Two different scalar witnesses span an affine line of polynomial pairs. Their agreement-set intersection is the set on which both received rows agree with that line’s joint polynomial pair. At most $e+1$ bad witnesses can lie on one line, by the disjoint fresh agreements of different points outside the common core. Thus a family of more than $e+1$ has a witness outside each such line. The outside polynomial agrees at at most $k-1$ sites of the line’s common core. Since it needs at least $t$ agreements in total, the common core has size at most $e+k-1$.

If $e\ge14$, select sixteen witnesses. Write $m_x$ for the number whose agreement sets contain $x$. Then $\sum_x m_x\ge16t$ and the diagonal and off-diagonal counts give $\sum_x m_x^2\le16n+240(e+k-1)$. Cauchy–Schwarz would force
$$
(16(n-e))^2\le n(16n+240(e+k-1)).
$$
For $k\le n/2$ and $e\le181823220$, the inequality goes the other way. At the worst corner the positive difference is 435257118720; raising $e$ by one changes that difference to $-279103244032$. The ordinary RS staircase supplies the same upper bound at $e<14$. The universal spike construction supplies $e+1$ bad scalars, since $e+1+k\le n$. Thus at integer errors $0\le e\le181823220$ the exact MCA error probability is $(e+1)/p$. The spike alone supplies the bad-endpoint lower bound also at $e=181823221$. Monotonicity, Hamming-step constancy and the interleaving theorem give the threshold. [Pair argument](../../../ArkLib/Research/ProximityGap/Frontier/RateQuarterPairOverlap.lean) · [Spike construction](../../../ArkLib/Data/CodingTheory/ProximityGap/UniversalSpikeFloor.lean)

## A single production-length example

The prime
$$
p=61250826226543930850155988052636038260206862337=(256\cdot180000000+136)2^{120}+1
$$
has exact budget $180000000$. Its Lucas certificate uses witness 3 and $p-1=2^{123}\cdot8521\cdot675977$. The residue $g=830666351068687365643932774045365468737521668$ has exact order $2^{30}$. For this field and subgroup the first bad error count is $180000000$ at all four rates, for every positive interleaving width. [Explicit four-rate certificate](../../../ArkLib/Research/ProximityGap/Frontier/FourRatePairBudget.lean)

The exact counts in this interval are also consequences of published estimates. With $R=n-k$, the staircase covers $3e\le R$. For the rest, $R+1\le3e$ and $2e<R$. One has $e>2^{27}$ and $R-2e>2^{27}$. Hence $e(e+2)(R-2e)>2^{81}>n(R-e)$, so the integral BCHKS criterion gives exactly $e+1$. The present certificate derives the result from the sixteen-witness intersection count within Lean, including primality, field normalization and the open real endpoint. [Chojecki, Theorem 5.2](https://eprint.iacr.org/2026/1463) · [BCHKS](https://eprint.iacr.org/2025/2055)
