# An exact-cardinality degree-four Paley clique pseudoexpectation

Let $p\equiv1\pmod4$ be prime, and let $G$ be the affine Paley graph. There is an absolute $c>0$ such that, for every sufficiently large $p$ and every integer $4\le k\le cp^{1/3}$, the Boolean clique equations and $\sum_v x_v=k$ admit a degree-four pseudoexpectation. It assigns the normalized singular ternary four-site count value one. Thus a degree-four sum-of-squares proof from these Boolean and cardinality equations cannot force this statistic close to $1/4$ at these sizes. Kunisky and Yu proved a lower bound of order $p^{1/3}$ for the unrestricted clique objective. We use their signed graph-matrix bounds to verify an explicit witness satisfying every exact-size contraction. [Kunisky–Yu, *A degree 4 sum-of-squares lower bound for the clique number of the Paley graph*](https://arxiv.org/html/2211.02713) · [Four-site count and Paley discrepancy](paley-four-site-rank.md)

## The moments and their contractions

Write $C_4$ for the number of four-cliques, and $q_U$ for the number containing $U$. For squarefree monomials of degree $j=|U|\le4$, set
$$
 y_U=\frac{\binom{k}{4}}{C_4\binom{k-j}{4-j}}q_U.
$$
Repeated variables reduce by $x_v^2=x_v$. One has $y_\emptyset=1$, and $y_U=0$ whenever $U$ contains a nonedge. Since $\sum_{v\notin U}q_{U\cup\{v\}}=(4-j)q_U$, the moments satisfy $\sum_v y_{U\cup\{v\}}=k y_U$ for every $j\le3$. Four-cliques have Paley matrix $J-I$ with determinant $-3$, so the expected singular count is exactly $C_4 y_4=\binom{k}{4}$, where $y_4=\binom{k}{4}/C_4$ is their common weight. Lean verifies the normalization and contractions for weighted blocks of any fixed size. [Lean block-moment identities](../../../ArkLib/Research/ProximityGap/Frontier/PaleyQuarticSlice.lean)

Write $A$ for the adjacency matrix and $d=(p-1)/2$ for its degree. Distinct vertices have $(p-5)/4$ or $(p-1)/4$ common neighbors according as they are adjacent or nonadjacent. Every triangle has $p/8+O(\sqrt p)$ common neighbors: expand the three factors $(1+\chi)/2$ away from their three roots and apply the quadratic-character bound to the squarefree cubic. The corrections at the three coincidences cost $O(1)$. There are $\asymp p^3$ triangles by the two-site counts, and summing their extensions gives $C_4\asymp p^4$. Thus on triangles
$$
 y_3=\alpha_3+O(k^3p^{-7/2}),\qquad
 \alpha_3=\frac{p y_4}{8(k-3)}=O(k^3/p^3),\qquad y_4=O(k^4/p^4).
$$
Vertex and edge transitivity and the contractions give $y_1=k/p$ and $y_2=2k(k-1)/(p(p-1))$ on every edge. [Paley parameters and character bound, Kunisky–Yu, Proposition 2.4 and Theorem 4.4](https://arxiv.org/html/2211.02713)

## Positivity on the exact slice

Let $E_{ef}=y_{e\cup f}$ on the unordered edges of $G$, $C_{ve}=y_{\{v\}\cup e}$, $V=y_1 I+y_2 A$, and $W_{ve}=\mathbf1_{v\in e}$. Moments indexed by nonedge pairs have zero rows. The contraction identities give $WE=(k-1)C$ and $WEW^\top=(k-1)^2 V$. In the full moment matrix, each singleton row is the sum of its incident pair rows divided by $k-1$, and the constant row is the sum of the singleton rows divided by $k$. These identities apply in every column by contraction. Consequently it suffices to prove $E\succeq0$. The least adjacency eigenvalue is $-(1+\sqrt p)/2$, so $V\succeq(k/(2p))I$ throughout the claimed range for large $p$.

Every pair vector is $u+W^\top a$ with $Wu=0$. Completing the square in $a$ shows that it suffices to prove
$$
 u^\top E u\ \ge\ (Cu)^\top V^{-1}(Cu)\qquad (Wu=0).             \tag{1}
$$
To estimate the right side, put $\mu=d^2/p^2$ and $Z_{(a,b),v}=A_{av}A_{bv}-\mu$ on all ordered pairs, including equal ones. Its column Gram entry is $\operatorname{codeg}(v,w)^2-d^4/p^2$, with $\operatorname{codeg}(v,v)=d$. The off-diagonal entries are $O(p)$ and the diagonal $O(p^2)$, hence $\|Z\|=O(p)$. Restrict to one orientation of each edge. Then $C=y_2W+\alpha_3(Z^\top+\mu J)+\mathcal E$, where the entrywise errors are $O(k^3p^{-7/2})$. At an incident pair the product $A_{av}A_{bv}$ vanishes and the $y_2W$ term is exact. The Frobenius norm gives $\|\mathcal E\|=O(k^3/p^2)$. Both $W$ and $J$ annihilate $u$, so the right side of (1) is $O(k^5/p^3)\|u\|^2$.

For the left side decompose $E=y_2 I+S+y_4D$. The matrix $S$ is supported on two different edges meeting at a vertex and forming a triangle. Up to error of norm $O(k^3p^{-5/2})$ by absolute row sums, it is $\alpha_3$ times the sum of the adjacency matrices on the neighbors of each vertex, lifted onto its incident edges. For each star, the least eigenvalue of the induced adjacency is at least $-(1+\sqrt p)/2$ by compression of $A$. Each edge occurs in two stars. Thus $S\succeq-O(k^3p^{-5/2})I$.

The disjoint-edge matrix $D$ indicates that $e\cup f$ is a four-clique. For $e=\{a,b\}$, $f=\{c,d\}$ disjoint, $16D_{ef}$ is the product of $1+\chi(i-j)$ over the four cross pairs. In its expansion, extend the constant, the four single signs, and the four products of two signs with a common endpoint to all edge pairs by the same formulas. Each extended sum vanishes as a quadratic form on $\ker W$: the constant matrix is $J$, the singles are $W^\top (\chi(i-j))_{ij} W$, and the common-endpoint products factor through $W$ on the row or column side. This extension can change the formula at a coincidence, since $(1+\chi(0))/2=1/2$ whereas $A_{ii}=0$. The difference is supported on $O(p)$ entries in each row and column, bounded by an absolute constant per entry, so it costs $O(p)$ in operator norm.

The remaining disjoint-support terms are exactly the signed perfect-matching sum $T^{4,2,3}$, the three-edge path sum $T^{4,3,1}$ and the four-edge product $T^{4,4,1}$ of Kunisky–Yu restricted to Paley edges. Their operator norms on all unordered vertex pairs are respectively $O(p)$, $O(p)$ and $O(p^{5/4})$ by Propositions 3.27, 3.25 and Theorem 3.35. Principal compression preserves the upper norm bounds. This proves $|u^\top Du|\ll p^{5/4}\|u\|^2$ on $\ker W$. [Graph-matrix formulas and bounds, Kunisky–Yu, §3.4–3.5](https://arxiv.org/html/2211.02713#S3)

Combining these estimates, the left side of (1) minus its right side is at least
$$
 \left[y_2-O\!\left(k^3p^{-5/2}+k^4p^{-11/4}+k^5p^{-3}\right)\right]\|u\|^2.
$$
Relative to $y_2\asymp k^2/p^2$, the three costs are $O(kp^{-1/2})$, $O(k^2p^{-3/4})$, and $O(k^3/p)$. The first two vanish uniformly for $k\le cp^{1/3}$, and choosing $c$ small absorbs the last. This proves positivity and the exact-slice claim. A pseudoexpectation need not come from a distribution on actual $k$-cliques.

## A finite witness outside the clique distribution polytope

At $p=137$ and $k=6$ the exact pseudoexpectation gives positive weight to $\{0,1,2,38\}$. Its common neighbors are exactly $16,19,39,74,101$. No two are adjacent, so no six-clique contains these four sites. Thus even though this pseudoexpectation has a positive definite edge block, no distribution on six-cliques realizes its moments.

Run `python3 -B scripts/probes/probe_paley_quartic_slice.py` to verify all cardinality contractions and positivity at $(p,k)=(29,4),(53,5),(137,6)$. After a common integer scaling, translation invariance gives a block-circulant edge matrix in midpoint coordinates. Negation makes each offset sequence even. Fourier transformation reduces positivity to real symmetric matrices whose entries are polynomials in $2\cos(2\pi j/p)$. The probe isolates every conjugate by rational sign changes, bounds the evaluation error using $|(2\cos(h\theta))'|\le h^2$ as a function of $2\cos\theta$, and subtracts a certified operator error before testing positive definiteness by fraction-free elimination. It checks 15, 27, and 69 frequency blocks, respectively, including the constant block and one from each conjugate pair. [Exact finite verifier](../../../scripts/probes/probe_paley_quartic_slice.py)
