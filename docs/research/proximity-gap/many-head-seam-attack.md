# An exceptional site for each polynomial head

Let a Reed–Solomon code have dimension $k$ on an arbitrary injective $n$-point domain in a finite field of cardinality $q$. Fix $2\le m\le k$, let $t=n-e$, and assume $t-1\ge k$ and $m(t-k)\le n-k$. If $q>m^2n^2$, one received pair has at least $m(e+1)$ distinct MCA-bad scalars. The field may have any characteristic.

Take $k-m$ common sites and write $H$ for their locator. Choose $m$ further sites with evaluation values $a_1,\ldots,a_m$. Set
\[
 L_i(X)=\prod_{j\ne i}(X-a_j),\qquad Q_i(X)=H(X)L_i(X).
\]
Each $Q_i$ has degree $k-1$. Before choosing two received rows, work in the vector space with independent coordinate vectors $v_i$ for the heads and $w_y$ for every leftover site $y$. Head $i$ is the vector polynomial $Q_i v_i$.

Assign $r=t-k$ private sites to each head, using $k+mr\le n$ sites in total. Receive zero at the common sites and at the $m$ exceptional sites, receive the owning head on private sites, and receive $w_y$ at each leftover $y$. Head $i$ agrees on $k-m$ common sites, all $m-1$ exceptional sites other than $a_i$, and its own $r$ private sites. These $t-1$ sites determine a scalar polynomial of degree below $k$ after any scalar projection.

At every other site $x$, subtract the received vector from head $i$. The resulting $m(e+1)$ differences are nonzero and pairwise projectively distinct.

* The difference at $a_i$ has singleton support $\{v_i\}$.
* At a private site owned by $j\ne i$ it has support $\{v_i,v_j\}$. For the same unordered pair, orientation changes only the overall sign. The ratio of the two entries in fixed order is $-L_i(x)/L_j(x)=-(x-a_j)/(x-a_i)$. This fractional linear map is injective away from its pole because $a_i\ne a_j$. Every site has only one owner.
* At leftover $y$ the support is $\{v_i,w_y\}$. It recovers both the head and the site.

Choose a linear form $b$ nonzero on all the displayed directions. Each direction forbids one hyperplane and there are fewer than $q$ directions. Normalize each vector $D$ by $b(D)$. The normalized vectors are distinct. A second form $a$ separates them since fewer than $q$ pairs of normalized vectors are involved. Both assertions follow from a hyperplane having exactly $q^{s-1}$ elements in dimension $s$. This also covers characteristic two.

Receive the two scalar projections by $a$ and $b$. The label $-a(D)/b(D)$ gives agreement of the folded word with the folded head on its defining $t-1$ sites and the indicated fresh site. On that support, any two simultaneous degree-below-$k$ per-row fits must equal the projected head entries since $t-1\ge k$. The fresh second-row disagreement $b(D)\ne0$ therefore witnesses the literal MCA bad event. The projection makes all labels distinct.

## Explicit two-parameter pencil

Put $T(X)=H(X)\prod_j(X-a_j)$. The scalar head with second row $Q_i$ has first-row pencil components $a_iQ_i$ and $a_i^2Q_i$. At a private site owned by $j$ receive that head. At any leftover site $x$ choose one virtual coefficient $c$ outside the whole domain and receive the three values $cT(x)/(x-c)$, $c^2T(x)/(x-c)$ and $T(x)/(x-c)$. Use $c=a_j$ at a private site owned by $j$. In either case the difference of the second coordinates at a fresh site is
\[
 Q_i(x)-T(x)/(x-c)=T(x)(a_i-c)/((x-a_i)(x-c))\ne0.
\]
The two normalized fresh labels for the first-row pencil are $-x$ and $-((a_i+c)x-a_i c)$. At the exceptional site $x=a_i$ they are $-a_i,-a_i^2$. The first component recovers the fresh site. At a fixed ordinary site the difference between two second components is $-(a_i-a_j)(x-c)\ne0$. A single scalar projection therefore separates all labels whenever their unordered-pair count is at most the field size, as in the Lean lemma `LinearPencilFreshLabels.separating_pair`. This derivation gives the same number of labels in every characteristic.

## Second production prime

At $n=2^{30}$ the named prime has bad-count budget $2n$. Each row below uses $e=\lceil(m-1)(n-k)/m\rceil$. At all three rates four or five exceptional points suffice for the displayed improvement by one error over the affine-head bound. The construction applies to every injective evaluation domain.

| Rate | Heads | Error count | Private sites per head | Leftover sites | Bad scalars |
|---|---:|---:|---:|---:|---:|
| $1/2$ | 5 | 429496730 | 107374182 | 2 | 2147483655 |
| $1/4$ | 4 | 603979776 | 201326592 | 0 | 2415919108 |
| $1/8$ | 4 | 704643072 | 234881024 | 0 | 2818572292 |

These are upper bounds on the first failing error counts. A field-specific matching bound below these counts remains open. [Finite-field witness and arithmetic checks](../../../scripts/probes/probe_many_head_seam_attack.py)
