# List budgets under row projection

Let $C$ be a linear code over the finite field $K$ of size $p$, and let $a$ be an integer agreement threshold on $n$ coordinates. Write $L_m$ for the largest number of words of the $m$-fold interleaving in a closed ball at this threshold. A coordinate agrees only when every row agrees. Assume $m\ge1$.

## The small-list equivalence

If $\binom{B+1}{2}\le p$, then $L_m\le B$ if and only if $L_1\le B$. To prove the forward implication, embed scalar words and their center diagonally. For the converse, suppose a ball contains $B+1$ distinct interleaved words. For each pair, the weights $\ell\in K^m$ that give the same scalar projection form a proper subspace. A coordinate at which the pair differs provides a nonzero defining linear equation. At most $p$ proper subspaces cannot cover $K^m$. Indeed, each contains at most $p^{m-1}-1$ nonzero vectors, and all share zero. Some single choice of $\ell$ separates the entire list. Linear projection preserves code membership and every coordinate of agreement. It gives $B+1$ distinct scalar codewords in the projected ball.

For $p<2^{256}$ and $B=\lfloor p/2^{128}\rfloor$, the hypothesis holds. The [Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListProjection.lean) uses the canonical closed-ball list definition. The equivalence determines the dependence of the prize budget on interleaving arity. Its numerical radius still depends on the scalar code.

## A width-independent threshold over every finite field

For a linear code over a field of size $q$, take an integer budget $B<q$. If a ball can contain only words with at most $E$ errors and $BE\le q$, then $L_m\le B$ if and only if $L_1\le B$. This holds at the same real radius for every positive width. In particular, with $B=\lfloor q/2^{128}\rfloor$, it holds at every radius on every domain of length at most $2^{128}$. It also applies on longer domains at radii admitting at most $2^{128}$ errors. The alphabet size is unrestricted. For example, the result applies on the original length-$2^{30}$ domain after extending either named prime field to any finite degree, with the budget computed from the new field size. Determining the scalar threshold remains necessary. [Lean theorems](../../../ArkLib/Research/ProximityGap/Frontier/InterleavedListProjection.lean)

Suppose all scalar balls meet the budget and an interleaved ball contains $B+1$ distinct words. On the agreement set of any listed word, its values determine it amongst all interleaved codewords. Otherwise some row of the difference of two such words would be a nonzero scalar codeword vanishing on that set. All $q$ multiples of the difference row would lie within the radius of the zero scalar center.

Choose $B$ of the listed words. In each of their mismatch columns, row weights that make the projected word agree with the projected center form a proper hyperplane. The total is at most $BE\le q$, so one weighting avoids every such hyperplane. All $B+1$ words retain their original agreements, and the selected $B$ retain their exact agreement sets. If two projections coincided, at least one of those words would be selected. Its exact agreement set would contain the original agreement set of the other, forcing the two original words to be identical. The projected scalar list therefore has $B+1$ distinct members. Diagonal embedding gives the converse.

## Extension fields

Suppose a Reed–Solomon evaluation domain is contained in $K$, and codeword coefficients belong to a finite extension $E/K$ of degree $d$. Writing each coefficient and each received symbol in a $K$-basis of $E$ identifies this code isometrically with a $d$-fold interleaving over $K$. Evaluations commute with the coordinate expansion since the domain lies in $K$. An $m$-fold interleaving over $E$ gives $dm$ rows over $K$. In a prize application the numerical budget remains $\lfloor |E|/2^{128}\rfloor$.

## Counting projected collisions

Put $L=L_1$. Fix any ball containing $M\ge1$ distinct interleaved codewords and choose a uniform $\ell\in K^m$. Their scalar projections occupy at most $L$ scalar words. If the occupied multiplicities are $b_j$, Cauchy–Schwarz gives $\sum_j b_j^2\ge M^2/L$. Every distinct pair collides with probability at most $1/p$. Counting ordered pairs including the diagonal yields
$$
 M^2/L\le M+M(M-1)/p,\qquad
 M(p-L)\le L(p-1).
$$
For a uniformly chosen nonzero row weighting, one may replace $1/p$ by $(p^{m-1}-1)/(p^m-1)$.

There is a stronger estimate for Reed–Solomon dimension $k$ when $a\ge k$. For two distinct interleaved codewords $v,w$, define their rank to be the dimension of the subspace of $K^m$ spanned by $(w-v)(x)$ across the evaluation domain. The projection collision probability is exactly $p^{-r}$ for rank $r$.

Fix $v$ in the ball. If $w-v$ has rank one, write $w-v=b f$ for a nonzero direction $b\in K^m$ and a nonzero scalar codeword $f$. Among the at least $a$ coordinates where $w$ agrees with the center $y$, at most $k-1$ have $w=v$. Every other such coordinate has nonzero residual $y(x)-v(x)$ on the line $Kb$. Residuals belonging to different lines use disjoint coordinates, and $v$ disagrees on at most $n-a$ coordinates. At most
$$
 D=\left\lfloor\frac{n-a}{a-k+1}\right\rfloor
$$
lines can therefore occur. For one such line choose a representative $b$ and a scalar center $g$ by solving $b g(x)=y(x)-v(x)$ wherever the residual belongs to $Kb$. Elsewhere set $g(x)=0$. Then $0$ and all the functions $f$ for neighbors on this line belong to the scalar list at $g$. Thus $v$ has at most $D(L-1)$ rank-one neighbors. All other off-diagonal pairs collide with probability at most $1/p^2$, giving
$$
 M(p^2-L)\le L\bigl[p^2-1+(p-1)D(L-1)\bigr].
$$

For example take $p=2130706433$, $E=\mathbf F_{p^6}$, $n=262144$, $k=131072$, and $a=181855$. Here $D=1$. With $B=\lfloor p^6/2^{128}\rfloor=274980728111395087$, the last inequality implies $M\le B$ if $L\le24204307687363$. This is a sufficient scalar list bound for that radius. The calculation gives no upper bound on $L$ itself.

More generally, for a rank-$r$ neighbor of $v$ let $U=\operatorname{span}\{(w-v)(x)\}$. Distinct possible $U$ can be counted through independent residuals. After selecting $j<r$ independent residuals on coordinates where $w=y$, their span has codimension $r-j$ in $U$. Apply a basis of the annihilator to $w-v$. This gives $r-j$ independent scalar degree-below-$k$ polynomials. If they have $s$ common zeros on the domain, divisibility by the common locator gives $r-j\le k-s$. Thus there are at least $a-k+r-j$ choices for the next residual outside the existing span. Each possible $U$ contributes at least $(a-k+r)_r$ ordered independent coordinate tuples, where $(z)_r$ denotes the falling factorial. Each tuple determines $U$ and uses only coordinates with $v\ne y$. The number of possible $U$ is at most
$$
 \left\lfloor\frac{\binom{n-a}{r}}{\binom{a-k+r}{r}}\right\rfloor.
$$
For a fixed $U$, projecting to a basis of $U$ represents its neighbors in one $r$-fold interleaved list containing zero. There are at most $L_r-1$ of them.

The [finite check](../../../scripts/probes/probe_interleaved_list_projection.py) enumerates every received coset on four small codes and verifies the pair-budget equivalence and the displayed collision inequalities.

Gopalan, Guruswami and Raghavendra give general list-size bounds for interleavings and use generalized Hamming weights to study low-rank codewords. Jo studies row projections for mutual correlated agreement and curve decodability. [List Decoding Tensor Products and Interleaved Codes](https://arxiv.org/abs/0811.4395) · [Interleaving Stability for Mutual Correlated Agreement and Curve Decodability](https://eprint.iacr.org/2026/891)
