# The ordinary mixed-jet dimension test at Johnson

For natural parameters $0<d\le n$ and $t^2\le nd$, the ordinary mixed Hasse interpolation support has at most as many unknown coefficients as equations, for **every** multiplicity $r$, scalar/value total-degree cutoff $s$, and value-degree cutoff $v$. Lean proves this inequality for the same `columnCount` and `rowCount` used to construct the production surfaces. At half rate it also compares the actual cardinalities of the two finite index types on any domain of the named size. An interpolant at this radius would need information about dependencies among the equations or a different interpolation construction. [Uniform theorem and finite index spaces](../../../ArkLib/Research/ProximityGap/Frontier/JohnsonJetRoom.lean) · [Half-rate production interpolation](half-sparse-gauss-window.md)

For length $n=2^{30}$ the first integer errors with squared agreement below $nd$, for $d=K-1$, are:

| Rate | $d$ | Largest agreement count with $t^2\le nd$ | First error count |
| ---: | ---: | ---: | ---: |
| $1/2$ | 536,870,911 | 759,250,124 | 314,491,700 |
| $1/4$ | 268,435,455 | 536,870,910 | 536,870,914 |
| $1/8$ | 134,217,727 | 379,625,061 | 694,116,763 |
| $1/16$ | 67,108,863 | 268,435,453 | 805,306,371 |

The second-prime half-rate written safety bound is **312,800,001** for the first failing count. The integer **314,491,700** above is a boundary for this interpolation argument. Both claims apply to injective domains of the stated length. [Half-rate safety proof and verification](half-sparse-gauss-window.md)

## Comparing every prefix of value degrees

Write $x_+=\max(0,x)$. The coefficient count is
\[
 \sum_{j=0}^{v}(s+1-j)_+(rt-jd)_+.
\]
The equation count is $n\sum_{j\ge0}(s+1-j)_+(r-j)_+$. For each prefix $0\le j<k$, compare the unweighted sums of $(rt-jd)_+$ and $n(r-j)_+$. The case $r=0$ gives zero columns. If $t<d$, raise the column agreement parameter to $d$, for which $d^2\le nd$. Assume $r>0$ and $d\le t$.

When $k\le r$, every summand before truncation is nonnegative. The doubled prefix inequality reduces after factoring $k$ to
\[
 2rt-d(k-1)\le n(2r-(k-1)).
\]
The Johnson hypothesis and $(t-d)^2\ge0$ imply $2t\le n+d$. The displayed difference on the right is the sum of $r(n+d-2t)$ and $(r-k+1)(n-d)$, both nonnegative.

When $k>r$, take $L=\min(k,\lfloor rt/d\rfloor+1)$. Then $L\ge r+1$, and the doubled coefficient prefix equals $2Lrt-dL(L-1)$. The doubled equation prefix is $nr(r+1)$. Put $B=r(r+1)$. Multiplying their difference by the positive number $Bd$ gives the identity
\[
 Bd\bigl(nB-2Lrt+dL(L-1)\bigr)
 = B^2(nd-t^2)+(Bt-rLd)^2+rL(L-r-1)d^2.
\]
All three terms on the right are nonnegative. This proves the comparison of every unweighted prefix.

Finally the weight $(s+1-j)_+$ counts the prefixes ending at $k\in\{1,\ldots,s+1\}$ which contain $j$. Adding their inequalities supplies exactly the stated scalar weights. Imposing the value cutoff $v$ can only reduce the coefficient count.
