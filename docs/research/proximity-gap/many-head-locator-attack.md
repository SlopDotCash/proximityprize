# More than three affine heads on an arbitrary evaluation domain

Let $\ell\ge2$, $2\le k<n$, and take an arbitrary injective $n$-point domain over a finite field of characteristic greater than $2\ell$ and cardinality greater than $\ell^2 n^2$. A single received pair has at least **$\ell(e+1)$ distinct MCA-bad labels** whenever
\[
 \ell e\ge(\ell-1)(n-k)+\ell-2,\qquad n-e-1\ge k .
\]
Consequently the following are upper bounds on the first failing counts on the second named prime at $n=2^{30}$, with budget $2n$. They use no property specific to its multiplicative domain.

| Rate | Number of heads | Error count | Distinct bad labels |
|---|---:|---:|---:|
| $1/2$ | 5 | 429496731 | 2147483660 |
| $1/4$ | 4 | 603979777 | 2415919112 |
| $1/8$ | 4 | 704643073 | 2818572296 |

In particular at rates $1/4$ and $1/8$ these beat the earlier upper count $715827882$ furnished by three heads. The five-head count exceeds the second budget by 12. These are upper witnesses; the matching safety steps remain open.

Put $t=n-e$ and choose $h=\max(0,\lceil(\ell(t-1)-n)/(\ell-1)\rceil)$ common sites. The error assumption gives $h\le k-2$. Write $H$ for their monic locator. Each of the $\ell$ heads takes $r=t-1-h\ge0$ disjoint private sites, leaving $\lambda=n-h-\ell r\ge0$ extra sites. For $i=0,\ldots,\ell-1$ let $b_i=i+1$, $a_i=b_i^2$ and use head pairs
\[
 H(X)(a_i X+c_i,b_i).
\]
Both entries have degree below $k$. Receive zero on the common sites and the designated head on each private set. A site $x$ private to $j$ gives every other head $i$ a fresh label
\[
 z_{ij}(x)=-\frac{(a_i-a_j)x+(c_i-c_j)}{b_i-b_j}.
\]
For one unordered type $\{i,j\}$ these labels are injective in $x$, since $a_i-a_j=(b_i-b_j)(b_i+b_j)\ne0$. For two different unordered types, the linear functionals of the vector $c=(c_0,\ldots,c_{\ell-1})$ have different supports. Thus an equality between two prescribed labels of these types excludes exactly one proper affine hyperplane. There are at most $\binom{(\ell-1)n}{2}<|\mathbb F|$ such hyperplanes. Their union cannot fill $\mathbb F^\ell$, so choose $c$ making all private fresh labels distinct.

At each extra site choose the received pair to be $H(x)(U,V)$ with $V\notin\{b_i\}$. Its scalar labels $(a_ix+c_i-U)/(V-b_i)$ are nonconstant affine functions of $U$ with mutually distinct slopes. Avoid the values giving a collision with an earlier label or with another new label. There are at most $\ell^2(e+1)+\binom{\ell}{2}<|\mathbb F|$ excluded values since $e+1\le n-1$, $\ell\ge2$, and $n>k\ge2$. This completes the construction.

Each fresh label for head $i$ agrees on that head's $t-1$ defining sites and at its fresh site. Any joint fit by two degree-below-$k$ polynomials on this support must equal the head's two polynomial entries because $t-1\ge k$. At the fresh site its second row differs, so the support is literally MCA-bad. Each head supplies $n-(t-1)=e+1$ such distinct labels. [Arithmetic and finite-field examples](../../../scripts/probes/probe_many_head_locator_attack.py)
