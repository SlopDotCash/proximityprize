# Incidence bounds for affine Reed–Solomon lists

Let $n=2^{30}$ and $k=2$. At the first designated prime every closed list has size at most $B_1=2^{30}$ when its words agree with the center on at least **3073 sites**. At the second prime the corresponding cutoff is **2439 sites** for $B_2=2^{31}$. Both assertions hold on every injective evaluation domain and at every positive interleaving width. These are upper bounds on list size, and the exact first failing counts remain open. The prize's four dimension choices at this length start at $k=2^{26}$.

## Counting the original scalar list

Suppose a center $u$ has $L=B+1$ distinct affine codewords agreeing with it on at least $t$ sites each. The set of $n$ points $(x,u(x))$ and the chosen $L$ graph lines $y=ax+b$ have at least $Lt$ incidences. Distinct codewords supply distinct pairs $(a,b)$. For the interleaved result, project the $L$ vector codewords by one common linear functional separating them. Each agreement coordinate survives, and $\binom L2\le p$ for both fields. [Scalar projection in Lean](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListProjection.lean)

For each integer $0\le d<p$, the discrete graph version of Lewko's theorem bounds the incidences between $m$ points and $l$ graph lines by
\[
C(m,l,d)=m\left(1+\left\lfloor\frac{2l}{d+2}\right\rfloor\right)+d(d-1)+l.
\]
One can use either $C(n,L,d)$ or $C(L,n,d)$. In the latter case map $(x,y)$ to the line with slope $x$ and intercept $-y$, and $(a,b)$ to the point $(a,-b)$. The incidence equation $y=ax+b$ is equivalent to $-b=xa-y$. [Lewko, arXiv:2609.27023v3](https://arxiv.org/abs/2609.27023v3) · [Author's discrete graph theorem](https://github.com/mrklwk/szemeredi-trotter-lean/blob/844228bc6c042e59373888d1b69f4e215d1c00e4/MathCollab/IncidenceSharper.lean#L18)

| Budget | Orientation | $d$ | Incidence upper bound | $t$ | $Lt$ |
|---:|---|---:|---:|---:|---:|
| 1,073,741,824 | Original | 1,048,575 | 3,299,605,479,427 | 3073 | 3,299,608,628,225 |
| 2,147,483,648 | Dual | 1,320,714 | 5,237,166,304,180 | 2439 | 5,237,712,619,911 |

Both upper bounds are strictly smaller than $Lt$. For comparison, the finite Johnson bound at these budgets requires **32769** agreements at each prime. The two incidence estimates establish safety at **1,073,738,751** and **1,073,739,385** errors respectively.

## Dimension three by one agreement anchor

For degree at most two, some site $x_0$ has at least $l=\lceil Lt/n\rceil$ agreeing words. Subtract $u(x_0)$ from each of those polynomials and divide by $X-x_0$. The $l$ resulting affine polynomials are distinct and each agrees with the transformed center $(u(x)-u(x_0))/(x-x_0)$ on at least $t-1$ of the remaining $n-1$ sites. Thus either orientation of the discrete bound can rule out the starting list if it gives fewer than $l(t-1)$ incidences. For the first named budget $t=75675$, $l=75676$ and $d=37837$ give $C(n-1,l,d)=5726643700<l(t-1)$. For the second, $t=62830$, $l=125661$ and $d=50263$ give $7895153682<l(t-1)$. Both bounds are weaker than the finite Johnson certificate for dimension three. At its cutoff of 46342 agreements at the first prime and 46342 at the second, neither orientation beats the required incidence count for any degree. To verify this last comparison with finitely many integer evaluations, for each quotient $\lfloor2l/(d+2)\rfloor$ use its smallest permissible $d$. When the quotient remains fixed the cost is nondecreasing in $d$. Apply the same calculation with the two cardinalities exchanged.

The same method improves Johnson at larger admissible field budgets. At $B=8n$ choose $t=44429$, $l=355433$ and $d=71085$. At $B=64n$ choose $t=26412$, $l=1690369$ and $d=120739$. The two incidence costs are 15,790,779,803 and 44,644,246,795 respectively, strictly below $l(t-1)$. Every prime with actual budget at least the displayed $B$ meets its 128-bit budget at that agreement count, on every injective domain and at every positive width. Since the finite Johnson thresholds at these two budgets are 46,342 and 46,341, the improvements are 1,913 and 19,929 agreements. Both bounds link to the external discrete theorem and pass the native axiom check. [Lean shortening and arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/QuadraticListIncidences.lean) · [Unconditional prime-field endpoints](../../../scripts/integration/lewko/AffineNamedEndpoints.lean)

## Reproducing the proof

The repository's conditional discrete-incidence consumer constructs the graph of the center, extracts a sublist of exactly $B+1$ codewords, dualizes the second configuration and applies scalar projection. The separate named-prime endpoints link that consumer to the author's fully proved `graph_discrete` declaration. The external project is distributed under AGPL-3.0-only. The verifier obtains the pinned, unmodified sources, compiles their import closure with this repository's Lean and mathlib, and checks both named affine endpoints and both quadratic endpoints. [Repository consumer](../../../ArkLib/Research/ProximityGap/Frontier/AffineListIncidences.lean) · [Named-prime proof](../../../scripts/integration/lewko/AffineNamedEndpoints.lean) · [External source and license](https://github.com/mrklwk/szemeredi-trotter-lean/tree/844228bc6c042e59373888d1b69f4e215d1c00e4)

From the repository root run `python3 scripts/integration/lewko/verify.py`. An existing clone can be supplied with `--source /path/to/szemeredi-trotter-lean`.
