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

## Sharpness for four exceptional heads with arbitrary received rows

At rates one eighth and one quarter, the respective named second-prime upper counts **704643072** and **603979776** are sharp among the four-head configurations below, even if several fresh matches support one label.

Take $s\ge0$ and a block of $b=k-s\ge4$ distinct domain points, four of them exceptional values $a_1,\dots,a_4$. Let $T$ be the block locator and let
\[
 W_i=W_0+\frac{T(X)}{X-a_i}\,(A_i(X),B_i(X)),\qquad
 \max(\deg A_i,\deg B_i)\le s .
\]
Here $W_0$ is a common polynomial pair. Assume the four evaluated heads are distinct at every site outside the block, and $(A_i(a_i),B_i(a_i))\ne(0,0)$. The explicit construction at the upper count belongs to the $s=0$ class. In its separating projection the four exceptional-site labels are distinct, which gives distinct scalar head directions. For $s=0$, arbitrary nonparallel constant head vectors satisfy these assumptions.

Fix arbitrary received rows. Let $C_i$ be their joint agreement set with head $i$, write $c_i=|C_i|$, and let $H$ count sites in none of the $C_i$. A scalar represented by head $i$ on a literal nonjoint witness must use at least $\max(1,t-c_i)$ sites outside $C_i$. Each such fresh site can support at most one scalar for its assigned head, because an affine equation in the scalar has at most one root unless both rows coincide. Thus head $i$ represents at most $e+1$ bad scalars, and at most $1+\lfloor e/2\rfloor$ if $c_i<t-1$.

Put $e_0=3(n-k)/4$ and check $e=e_0-1$, the worst predecessor by monotonicity. If at most two cores have size $t-1$ or larger, assign each label to a representing head. At most $2(e+1)+2(1+\lfloor e/2\rfloor)\le3e+4<2n$ labels can be assigned at either rate. Otherwise, write $C_4$ for the remaining core. The largest multiplicity at an ordinary site is one, at each of the four exceptional sites it is three, and at the remaining block sites it is four. Every uncovered site loses at least one from these multiplicity bounds. Hence
\[
 \sum_i c_i\le n+3b-4-H,\qquad
 t-c_4\ge 4t-n-3b+1+H=5+3s+H .
\]

Away from up to seven exceptional scalars, an ordinary fresh agreement for head 4 at a site belonging to $C_j$, $j\ne4$, must satisfy
\[
 (A_4+\gamma B_4)(X)(X-a_j)=(A_j+\gamma B_j)(X)(X-a_4).
\]
For each $j$, an identity of these two polynomials can occur for at most one scalar because an identity at two scalars would equate the underlying pairs as rational functions, contradicting their distinct exceptional values at $a_4$. Exclude those at most three scalars and the at most four scalars annihilating the nonzero exceptional-site head directions. For every remaining scalar, at most $3(s+1)$ ordinary fresh sites can belong to another core by the univariate root bound. A fresh match at a block site either lies in none of the cores or would annihilate that site's exceptional direction. Including the $H$ uncovered sites gives at most $H+3s+3$ fresh agreements, strictly fewer than required. Consequently this fourth head contributes at most seven further labels, so at most $3(e+1)+7<2n$ labels are represented.

At $s=0$ with nonparallel constant vectors, no pair of folded heads can coincide identically: an identity forces the two scalar coefficients to vanish together. The exceptional-scalar count then improves from seven to four. The argument applies on every domain. An earlier unrestricted failure can use more heads or heads outside these hypotheses.
