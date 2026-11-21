# A uniform MCA bound through unique decoding

Let $H$ consist of $n$ distinct elements of a finite field, and take the dimension-$k$ Reed–Solomon code with $1\le k<n$. Write $M_e$ for the maximum number of MCA-bad finite scalars at $e$ Hamming errors over all received pairs. For $1\le e\le(n-k)/2$, define
$$
S_e=n-k+1-2e,\qquad
m_e=1+\left\lfloor\frac{n-e}{n-k+1-e}\right\rfloor .
$$
Then
$$
M_e \le
\max\!\left(e+1,\ m_e\big(1+\lfloor e/S_e\rfloor\big)\right).
\tag{1}
$$
The bound applies to every evaluation domain. On an order-$2^{30}$ subgroup, it gives an exact rate-quarter threshold for every $128$-bit field budget between 402,653,184 and 805,306,369 bad scalars. It also determines all four official-rate MCA thresholds on each of the two explicit prime fields below.

## Proof of the uniform bound

Put $d=n-k-1$. For a received pair with more than $e+1$ bad parameters, the catalecticant and the minimal generic apolar form give a divisor $D$ of bidegree $(l,r)$ with $r\le e$ and nonzero-divisor syndrome section $W$ of $\mathcal O_D(l+1,r-2-d)$. When $d=2e-1$ the degree-$e$ catalecticant has fewer rows than columns, so its nonzero kernel is automatic. Otherwise it follows from the vanishing of its maximal minors at more than $e+1$ parameters. In all cases $d\ge2e-1$, which is enough for minimality and for interpolation on the union of the error support and each specialized divisor. The section degree gives $(d-2r+2)l\le r$. Thus $l\le\lfloor e/S_e\rfloor$.

Let $K$ be the degree-$n$ domain vanisher and $S$ the parameter vanisher of the $M$ bad scalars. The basic identity $KW_\gamma=0$ on every bad fiber allows division $W^m K/S$ for every integer $m\ge1$. If $K$ is identically zero on $D$, its fixed reduced support gives at most $r$ bad parameters by uniqueness of the decoded word. The remaining case gives a nonzero section of
$$
\mathcal O_D(m(l+1)-M,\ n-m(d+2-r)).
$$
Such a section must have nonnegative parameter degree whenever its coordinate degree is strictly less than $r$, by the ideal sequence in the [rate-half proof](rate-half-apolar-predecessor.md). In the [polynomial proof](rate-half-apolar-polynomial-proof.md), the same statement uses interpolation and reciprocal polynomials, changing the power three to $m$.

The real ratio $(n-r)/(d+2-r)$ is nondecreasing in $r$, since $n-(d+2)=k-1\ge0$ and the denominator is positive. Therefore $m=m_e$ satisfies $m(d+2-r)>n-r$, and the coordinate degree is strictly less than $r$. This gives $M\le m_e(l+1)$ and proves (1). The zero-pencil and proportional-pencil cases are covered as in the rate-half proof.

## Exact endpoint for rates through one third

Suppose $n-k=2a$, $a\ge2$, $k\ge2$, and $3k\le n+2$. Then $m_a=2$ since $n\le3a+1$, and monotonicity gives $m_e\le2$ for every $e\le a$. At $e=a$ the slack is one, so (1) gives $M_a\le2a+2$. For $1\le e<a$ the slack is at least three and $2(1+\lfloor e/3\rfloor)\le e+1$. In this range $M_e\le e+1$. For $e=0$, two distinct scalars with zero syndrome would put both received words in the code, so the upper bound one holds.

The bound $e+1$ is attained for $0\le e<a$: put the pair $(0,0)$ on $n-e-1\ge k$ points and $(-x,1)$ on every remaining site $x$. The scalar $\gamma=x$ has the all-zero mixed polynomial on the core and that site. Both rows would have to vanish identically to give a joint explanation on that same witness.

For the upper endpoint $a$, choose two disjoint exceptional sets of size $a+1$ in $H$, possible since $k\ge2$. Take the vanisher $V$ of their common complement, of degree $n-2a-2=k-2$. Use the two heads $(0,0)$ and $(XV,-V)$, both of degree at most $k-1$, with the second received only on the first exceptional set. Each head agrees jointly on $n-a-1=k+a-1$ points. Every exceptional $x$ supplies the scalar $\gamma=x$ for its head, a fresh agreement and a witness with no joint explanation. These $2a+2$ scalars are all distinct. Only distinctness of the domain points enters this construction.

It follows that $M_e=e+1$ for $0\le e<a$, and $M_a=2a+2$. For a budget $0\le B\le2a+1$, the first bad Hamming error count is $\min(B,a)$, including the endpoint cases. The good real radii end immediately below that grid point. When $B=0$ even the zero radius fails.

## Production fields and all four rates

Set $n=2^{30}$ and $h=n/4$. At rate $1/4$, the exact numerator at $e=3n/8-1$ is 402,653,184, and at $e=3n/8$ it is 805,306,370. At rates $1/8$ and $1/16$ the same general result gives the corresponding endpoint and all preceding counts. The integral BCHKS result already gives the exact quarter predecessor. The new quarter upper bound here concerns the endpoint itself. The earlier rate-sixteenth ledger also contains the production-rate-sixteenth staircase. [Earlier exact curve](../../../ArkLib/Research/ProximityGap/Frontier/_TwoLineSpikeThreshold.lean)

The following counts are first bad errors at tolerance $2^{-128}$. Each row uses one prime field and a single subgroup of order $2^{30}$. The rate-half entry uses its $h+2$ universal predecessor bound. The lower three rates use the general result above.

| Prime field | Budget | Rate $1/2$ | Rate $1/4$ | Rate $1/8$ | Rate $1/16$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $91343853062927602073649116268957764822404956161$ | 268435458 | 268435456 | 268435458 | 268435458 | 268435458 |
| $137015778580855056324475321314283763769844695041$ | 402653184 | 268435456 | 402653184 | 402653184 | 402653184 |

For the second row, $p=103079215165\cdot2^{120}+1$, the Proth witness is $3$, and $3^{(p-1)/2^{30}}$ is the order-$2^{30}$ element 92365554320529815296747239188837152885411596825. All displayed first bad errors are positive. Their immediately preceding integers pass, and each relative supremum is the displayed count divided by $2^{30}$. The named original production fields have different budgets. For every positive finite interleaving width the same MCA thresholds follow by exact interleaving stability. The unified safe-side proof is a written proof. Lean verifies the second field, its subgroup order and the bad-side numerator at $3/8$. [Quarter field certificate](../../../ArkLib/Research/ProximityGap/Frontier/RateQuarterApolarBudget.lean) · [Interleaving stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean)
