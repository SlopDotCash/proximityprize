# Branch orders forced by three complete subgroup fibers

On the first prime at 447,392,428 quarter-rate errors, write a candidate pencil as $V\circ W\circ U$, where $U$ has degree $h\in\{1,2\}$ and $W$ is the first primitive factor after that prefix. Write $m=\deg W$ and $t=hm$. Let $b_1,\ldots,b_r$ be its geometric inertia orders and put $E=\sum_i(1-1/b_i)-2$. With $D=268435454$ and $n=2^{30}$, the following necessary inequality holds:
\[
 E\ \ge\ \frac{2(D^3-8hn^2)}{4n^2(t+h)-D^3}.
\]
In particular a $(2,3,7)$ triangle cover is impossible at all four possible prefix degrees, for either type of quadratic inner map. The table takes the weaker bound when both $h=1,2$ are permitted. [The primitive factor and allowable degrees](quarter-split-pencil-pullbacks.md#a-primitive-factor-must-have-alternating-or-symmetric-monodromy)

| Prefix degree $t$ | Strict lower bound on $E$ | Consequence for three branch points |
| ---: | ---: | --- |
| 19,173,961 | 0.559999 | No inertia generator has order two. Neither $(3,3,c)$ nor $(4,4,c)$ occurs for any $c$. |
| 38,347,922 | 0.245613 | No $(2,3,c)$ occurs. A $(2,4,c)$ signature requires $c\ge228$. |
| 134,217,727 | 0.064516 | A $(2,3,c)$ signature requires $c\ge10$. |
| 268,435,454 | 0.031746 | A $(2,3,c)$ signature requires $c\ge8$. |

## A variance bound on the ordered-pair genus

Let $Y$ be the smooth projective normalization of the ordered distinct-pair curve of $W$. Its degree over the target is $m(m-1)$. It is connected by double transitivity of the geometric monodromy. The two coordinate maps $y_1,y_2$ to the source of $W$ both have degree $m-1$.

For each nonidentity power of the $i$th branch permutation give that power weight $w=1/b_i$, and write $F$ for its number of fixed sheets. The weights sum to $E+2$. Burnside's formula for cycles and Riemann–Hurwitz in the degree-$m$ action give $\sum wF=mE+2$. A permutation fixing $F$ sheets fixes $F(F-1)$ ordered distinct pairs. Applying the same two formulas in the pair action gives
\[
  2g(Y)-2=m^2E+2-\sum wF^2.
\]
Weighted Cauchy–Schwarz bounds the last sum below by $(mE+2)^2/(E+2)$. Exact cancellation gives
\[
  2g(Y)-2\ \le\ \frac{2(m-1)^2E}{E+2}.
\]
This bound uses only genus zero, tame ramification and double transitivity. [Lean weighted variance calculation](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitBranchOrders.lean)

## Pulling the two coordinates back to the subgroup

Over $Y$ take the normalization of $U(x_1)=y_1$, $U(x_2)=y_2$, with components $X_j$ of degrees $d_j$ over $Y$. The sum of the $d_j$ is $h^2$. On $X_j$ each coordinate $x_i$ has degree $a_j=d_j(m-1)/h$, hence $\sum_j a_j=h(m-1)$. Write $S_j$ for the zeros and poles of the two coordinates on $X_j$ and $\chi_j=2g(X_j)-2+|S_j|$.

For $h=1$, $\sum\chi_j\le 2g(Y)-2+4(m-1)$. For $h=2$, the quadratic cover $U$ has two branch values. Ramification of the pullback can occur at at most $4(m-1)$ places of $Y$, accounting for both coordinates. Each component comes from a compositum of at most two quadratic extensions. Its tame cyclic inertia has order at most two. Across the entire degree-four pullback the total ramification above each such place is at most two, including places at which both quadratic extensions ramify. Also $\sum_j |S_j|\le4\sum_j a_j=8(m-1)$. Riemann–Hurwitz therefore gives, for both values of $h$,
\[
  \sum_j\chi_j\le h^2\big(2g(Y)-2+4(m-1)\big).
\]

On each $X_j$ the two coordinates are multiplicatively independent modulo constants. Indeed a dependent component in the $x_1,x_2$ plane is a torus coset. After parametrizing it and comparing the degrees of $(W\circ U)(x_1)$ and $(W\circ U)(x_2)$, it must be a scaling or reciprocal graph preserving $W\circ U$, hence the full pencil. If $h=2$, the unique possible such nonidentity symmetry is already the involution of $U$, whose graph has $y_1=y_2$ and was removed. For $h=1$ it would be a nonidentity deck transformation of $W$, while the centralizer of the natural $A_m$ action is trivial. The identity graph is excluded in both cases. [Source-symmetry proof](quarter-split-pencil-pullbacks.md#a-source-symmetry-is-unique-if-it-exists)

There are at least $3Dh(m-1)$ ordered pairs of subgroup points lifted by these curves. Indeed each of the $3D$ points in the three full fibers has exactly $h(m-1)$ choices for a second point with the same value of $W\circ U$ and a different value of $U$. Complete splitting ensures these points are unramified; distinct pairs contribute separately.

Apply Corvaja–Zannier's gcd bound on $X_j$ to $x_1^n,x_2^n$. These functions are separable and have heights $na_j$. Their multiplicative independence gives $\chi_j>0$. The characteristic correction $12n^2a_j^2/p$ is below one, and the remaining term is $(54n^2a_j^2\chi_j)^{1/3}$. Hölder's inequality gives $\sum_j(a_j^2\chi_j)^{1/3}\le(\sum_j a_j)^{2/3}(\sum_j\chi_j)^{1/3}$. Thus
\[
 (3Dh(m-1))^3\le54n^2 h^4 (m-1)^2\big(2g(Y)-2+4(m-1)\big).
\]
Before using the signature, this gives an unconditional genus floor
\[
 g(Y)\ge\left\lceil 1+\frac{m-1}{2}\left(\frac{D^3}{2hn^2}-4\right)\right\rceil.
\]
For example the off-diagonal curve of every such primitive stage has genus at least **40,210,669,315,222**, the smallest of the four floors after allowing both possible source degrees. Dividing by $27h^3(m-1)^3$ and applying the pair-genus bound gives $D^3\le2hn^2(2(m-1)E/(E+2)+4)$. Rearrangement gives the claimed inequality. Its denominator is positive already at the smallest $t$. [Corvaja and Zannier, Theorem 2](https://doi.org/10.4171/JEMS/409) · [Lean numerical bounds](../../../ArkLib/Research/ProximityGap/Frontier/QuarterSplitBranchOrders.lean)

The function-field and group-action applications are written above. Lean verifies the weighted genus inequality, its combination with the torsion estimate, and the four numerical thresholds. An independent finite check computes both permutation actions explicitly for 620 generating triples of symmetric groups and reproduces the named rational bounds. [Finite verification](../../../scripts/probes/probe_quarter_split_branch_orders.py)
