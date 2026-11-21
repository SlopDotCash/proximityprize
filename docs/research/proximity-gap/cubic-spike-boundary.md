# Exact MCA thresholds at the two quarter-length budgets

Let $n=2^{30}$. For a finite field $F$ and security target $2^{-128}$, write $B=\lfloor |F|/2^{128}\rfloor$. The first failing error count on **every injective Reed–Solomon evaluation domain** has the following values. At every positive interleaving width, including width one, a real radius $\delta$ passes exactly when $\delta<B/n$. [Lean theorem](../../../ArkLib/Research/ProximityGap/Frontier/CubicSpikeBudgetBoundary.lean)

| Integer budget $B$ | Dimension $k$ | First failing error count |
|---:|---:|---:|
| 268435456 | $0\le k\le 536870911$ | 268435456 |
| 268435457 | $0\le k\le 536870909$ | 268435457 |

## Proof

At an arbitrary length $n$, put $e=B-1$ and $d=n-k-1$. If $B\ge6$, $k\ge1$, $k+2B\le n$, and $3k+2B<2n+5$, the cubic apolar estimate bounds the bad scalar count by

$$
\max\left(B,\;3\left(\left\lfloor\frac{B-1}{n-k+3-2B}\right\rfloor+1\right)\right).
$$

When $k+2B<n$ the denominator is at least four, so the maximum is $B$. When $k+2B=n$ the denominator is three and the maximum is $B$ if $3\mid B$. In either case the predecessor passes. At $B$ errors the spike gives at least $B+1$ bad scalars. Thus the first failing count is exactly $B$ for any positive security denominator $Q$ with $B=\lfloor |F|/Q\rfloor$. In particular, at $n=4B$ with $3\mid B$ the result applies at the full half-rate dimension $k=2B$. [Cubic apolar count](../../../ArkLib/Research/ProximityGap/Frontier/CubicApolarExtremum.lean) · [Spike witness and product criterion](../../../ArkLib/Research/ProximityGap/Frontier/LinearFieldBudgetRadius.lean)

For $k=0$ the code consists only of the zero word. Fix a bad scalar $b$ and one of its witness sets $S$. Every other bad scalar cancels a nonzero second-row entry outside $S$, and each coordinate gives at most one such scalar. This gives at most $1+(n-|S|)\le e+1$ bad scalars. The spike attains $e+1$ for every $0\le e<n$, so the table includes the zero code as well.

At $B=n/4$ and $k=n/2-1$, the existing product criterion requires $n<4B$, and the cubic inequality proves the missing equality case. At $B=n/4+1$ the product criterion already covers the displayed range. The two-budget table ends below half rate. At half rate on a specific noncoset domain of budget 268435457, an earlier construction gives an exact first failure of 268435455. The named production primes have different budgets, $n$ and $2n$. [Noncoset construction and subgroup scope](cubic-apolar-sharpness.md)
