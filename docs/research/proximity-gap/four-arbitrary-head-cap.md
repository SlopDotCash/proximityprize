# Four arbitrary polynomial heads at the second-prime budget

On an arbitrary injective domain of length $n=2^{30}$ over any finite field, four affine polynomial heads of dimension $k=n/8$ can represent at most $2n$ distinct MCA-bad scalars through **671088639 errors**. At $k=n/4$ this conclusion holds through **536870911 errors**. Received rows are arbitrary. Individual labels may require arbitrarily many fresh agreements.

Here a head is a pair $W_i=(A_i,B_i)$ of degree at most $d=k-1$. It represents a bad label $\gamma$ when the polynomial $A_i+\gamma B_i$ realizes a bad witness for those two fixed rows. Write $C_i$ for all sites where the two rows equal $W_i$, $I=\sum_i|C_i|$, and $U=|\bigcup_i C_i|$. Four coincident heads can be reduced to a smaller family. At each error count considered, three heads represent at most $3(e+1)<2n$ labels, so only four distinct heads need consideration.

## Core multiplicity

If the four heads are not all collinear over the function field, then $I\le n+4d$.

If no three heads are collinear, each of the four triple determinants with rows $(1,A_i,B_i)$ is a nonzero polynomial of degree at most $2d$. At a site where $j$ of a triple belong to the core, subtract one matching row from each of the others. The determinant vanishes to order at least $\max(0,j-1)$. Over all four triples, a site in two, three, or four cores contributes at least two, five, or eight. These dominate twice the multiplicity minus two, so $2(I-U)\le8d$.

Suppose three heads are collinear but the fourth lies off their line. Subtract the first head and divide a nonzero difference by the gcd of its two polynomial entries. This gives a primitive vector $V$ whose coordinate polynomials are coprime. Write the three heads as $W_1+Vf_i$, with $f_1=0$. The $f_i$ are polynomials because a polynomial linear combination of the two entries of $V$ equals one. With $r$ the maximum degree of those entries, every difference $f_i-f_j$ has degree at most $d-r$. The total excess of the three core sizes over the size of their union is at most the sum of their pairwise intersection sizes, hence at most $3(d-r)$. Indeed the primitive vector cannot vanish in both coordinates at a site. Each site where the fourth core meets that union is a zero of $\det(V,W_4-W_1)$, a nonzero polynomial of degree at most $d+r$. Thus $I-U\le3(d-r)+(d+r)\le4d$.

If all four heads are collinear, one can instead bound the number $M$ of distinct represented bad labels by $4n-3U$. Assign each label to one representing head and choose one fresh site with a row mismatch. At a site matching any head, all evaluated heads are on a common affine line through the received pair and therefore yield at most one scalar causing a fresh folded agreement. This conclusion also holds if all four evaluated heads coincide. Each remaining site can yield at most four assigned labels. In addition $3U\ge2I-6d$. At every covered site with multiplicity $j$, one has $2j-3\le\binom j2$, and each pair of distinct heads coincides on at most $d$ domain points. In particular, $I>n+4d$ implies $M<2n$ in this last case as well.

## The error counts

Assume $M\ge2n+1$ and put $t=n-e$. If a head with core $c$ receives $L$ different labels, their disjoint fresh sites imply $L\max(1,t-c)\le n-c$. A head has at most $e+1$ labels, and a head with $c\le t-2$ has at most $1+\lfloor e/2\rfloor$. When $3e+4\le2n$, at least three heads therefore have $c\ge t-1$. Every head receives at least $L_0=2n+1-3(e+1)$ labels. For $L_0>1$ this yields
\[
 I\ge3(t-1)+t-\left\lfloor\frac e{L_0-1}\right\rfloor .
\]
The following are the exact predecessor values. The last bound contradicts the core multiplicity result. A bad support at any smaller error count meets the larger count's size requirement, so the conclusion applies throughout each stated range.

| Rate | $e$ | $L_0$ | $\lfloor e/(L_0-1)\rfloor$ | Lower bound on $I$ minus $n+4d$ |
|---|---:|---:|---:|---:|
| $1/8$ | 671088639 | 134217729 | 4 | 1 |
| $1/4$ | 536870911 | 536870913 | 0 | 5 |

At rate one quarter the simpler size bound $4(e+1)\le2n$ already covers the indicated predecessor. At rate one eighth some injective domains over finite extensions attain all four personal capacities at 671088640 errors, making the predecessor sharp when the field and domain may vary. The production second-prime subgroup requires a separate construction. [Finite-extension sharpness](four-head-extension-sharpness.md) The exceptional-head result identifies a subclass whose first four-head failure is exactly 704643072. Families of more than four heads are outside this bound. [Exceptional heads](many-head-seam-attack.md) · [Endpoint arithmetic](../../../scripts/probes/probe_many_head_seam_attack.py)
