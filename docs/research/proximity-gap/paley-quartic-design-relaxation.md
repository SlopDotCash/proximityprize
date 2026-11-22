# An exact-size relaxation for prescribed Paley rank minors

For every sufficiently large odd prime $p$ and every integer $4\le k\le c p^{3/8}$, the degree-four Boolean sum-of-squares relaxation on the **affine** field with the exact equation $\sum_x X_x=k$ admits a solution assigning **100%** of its four-site mass to singular ternary Paley minors. It also admits one assigning **0%** to those minors. The same statements hold on the projective line. An elementary norm estimate alone gives both solutions through $k\le c p^{1/4}$. The $3/8$ exponent uses a Kloosterman correlation estimate. In particular both directions remain possible even when one requires nonnegative probabilities for every assignment on at most four sites.

The objective is the mass of singular minors divided by $\binom{k}{4}$. The variables in this relaxation mark the sites of the proposed subset and satisfy the Boolean equations through degree four. These witnesses address that rank objective directly. The related clique witness on primes $1\bmod4$ additionally sets every nonedge product to zero and reaches $k\le c p^{1/3}$. The construction here keeps the usual uniform pair moments, including positive moments on nonedges. [Rank criterion](paley-four-site-rank.md) · [Exact-size clique relaxation](paley-quartic-slice.md)

## The two quartic designs

Use $V=\mathbb P^1(\mathbb F_p)$ and $v=p+1$. For homogeneous representatives $u_x$ write $S_{xy}=\chi(\det(u_x,u_y))$. Choose $u_x=(x,1)$ and $u_\infty=(1,0)$. Put $\epsilon=\chi(-1)$. On distinct sites let $C_1,C_2,C_3$ be the products of the four directed $S$ entries along the three unoriented Hamilton cycles. Reversing a cycle preserves its product. The indicator $B$ that the principal minor is singular modulo three is
$$
 B=\tfrac14(1+\epsilon(C_1+C_2+C_3)).
$$
Indeed the cycle sum is $3\epsilon$ on the distinguished cross-ratio type and $-\epsilon$ otherwise. The singular blocks form a $3$-design, with $\lambda=(p-2-3\epsilon)/4$ completions of every triple and density $\theta=\lambda/(p-2)$. These statements follow from projective invariance and the complete two-point character sum. The complement is another $3$-design. In the proof let $H$ be either collection, and let $\rho=\theta$ or $1-\theta$, respectively. Both densities stay bounded away from zero for sufficiently large $p$. [Design parameters and proof](paley-rank-design.md) · [Determinant identity](paley-four-site-rank.md#exact-normalization-and-the-four-site-determinant)

Let $n$ be the ground size and $u_j=(k)_j/(n)_j$ for $0\le j\le4$, using falling factorials. A pseudoexpectation is determined by values $y_T=L(\prod_{i\in T}X_i)$ for $|T|\le4$ after Boolean reduction. On the projective line set $y_T=u_{|T|}$ for $|T|\le3$ and
$$
                          y_T=u_4\,\mathbf1_{T\in H}/\rho\quad(|T|=4).
$$
The $3$-design gives every exact-cardinality contraction $\sum_{j\notin T} y_{T\cup\{j\}}=(k-|T|)y_T$ through $|T|=3$. In particular $y_\varnothing=1$ and $\sum_{|T|=4}y_T=\binom{k}{4}$.

On the affine field take the same formula for $|T|=4$ with $n=p$. It remains normalized because the one-site design implies the fraction of blocks avoiding infinity equals the fraction of all four-sets avoiding infinity. For $|T|=t<4$ define
$$
        y_T=\binom{k-t}{4-t}^{-1}\sum_{U\supseteq T,\ |U|=4} y_U .
$$
Counting the $4-t$ possible sites to adjoin verifies all contractions. The affine group acts doubly transitively and preserves the blocks, so $y_T=u_t$ for $t\le2$. For an affine triple,
$$
  y_T=u_3\left(1+\frac{\rho-\mathbf1_{T\cup\{\infty\}\in H}}{\rho(p-3)}\right).
$$
This subtracts the single possible completion at infinity from $\rho(p-2)$ projective completions. Consequently the triple perturbation is $O(u_3/p)$ uniformly.

## Positivity reduces to the matrix on pairs

For an exact-size degree-four functional with $k\ge2$, the full moment matrix is positive semidefinite if its pair-by-pair principal block is. Against every test monomial of degree at most two the contractions give
$$
 X_i\equiv\frac1{k-1}\sum_{j\ne i}X_iX_j,\qquad
 1\equiv\binom k2^{-1}\sum_{i<j}X_iX_j .
$$
For the first identity use the size constraint against $X_i$ times the test monomial, of degree at most three. For the second, sum the first identities and use the size constraint again. Thus the full moment matrix is a linear image $RMR^\top$ of its pair block $M$. Necessity follows by taking a principal submatrix. [Lean singleton and constant contractions](../../../ArkLib/Research/ProximityGap/Frontier/PaleyQuarticSliceContractions.lean)

For the ordinary uniform $k$-slice, the pair block is
$$
 U=(u_2-2u_3+u_4)I+(u_3-u_4)W^\top W+u_4\mathbf1\mathbf1^\top ,
$$
where $W$ is the vertex-by-pair incidence matrix. In particular $U\succeq(u_2-2u_3+u_4)I$. The first coefficient is exactly $u_2(n-k)(n-k-1)/((n-2)(n-3))$, comparable to $u_2$ in our range.

Index pairs on the projective line. For disjoint $I,J$ let $K_{I,J}=\mathbf1_{I\cup J\in H}-\rho$ and set all other entries to zero. In the projective model $M=U+(u_4/\rho)K$. The product $KW^\top$ vanishes because each star outside $I$ gives the centered sum over all completions of a fixed triple. A vertex inside $I$ contributes nothing. On affine ground,
$$
 M=U+(u_4/\rho)K_{\mathrm{aff}}+E .
$$
Here $K_{\mathrm{aff}}$ is a principal submatrix of $K$. Only pairs sharing exactly one vertex contribute to $E$, with each entry $O(u_3/p)$ by the triple formula. Each row has at most $2(p-2)$ such entries, so $\|E\|=O(u_3)$.

## Norm of the disjoint-pair matrix

The projective character matrix satisfies $SS^\top=pI$. Distinct finite rows have finite-site inner product $-1$ and infinity adds $1$. The infinity row has zero inner product with every finite row. Thus $\|S\|=\sqrt p$.

It suffices to bound $K$ for singular blocks, since the complement negates it. On disjoint pairs the cycle formula writes $K$ as $(1/4-\theta)$ times the disjointness matrix plus $\epsilon/4$ times the three cycle matrices. The first summand has norm $O(p)$ by its row sum and $1/4-\theta=O(1/p)$. Order the elements of each pair in any fixed way, $I=(a,b), J=(c,d)$. Two cycles have factors $S_{ab}S_{cd}$ times one of $S_{ac}S_{bd},S_{ad}S_{bc}$ and a fixed sign. Before the disjointness restriction each matching matrix is a row/column restriction of $S\otimes S$ up to diagonal signs and a permutation, so its norm is at most $p$. Removing entries from overlapping pairs costs $O(p)$ since there are at most $2v$ entries of magnitude at most one per row and column.

The last cycle has entries $S_{ac}S_{ad}S_{bc}S_{bd}$, already zero for intersecting pairs. Its affine block is precisely the matrix in Kunisky–Yu, equation (112). Their Theorem 3.35 gives norm $O(p^{5/4})$ for primes $1\bmod4$. Its projective extension has zero block on pairs containing infinity. The cross block indexed by $\{\infty,a\}$ and $\{c,d\}$ has entry $\chi(a-c)\chi(a-d)$. Its squared row norm is $\binom{p-1}{2}$ and the inner product of two distinct rows is $(3-p)/2$. For the latter, put $h(c)=\chi(a-c)\chi(b-c)$ and use $\sum h=-1$, $\sum h^2=p-2$. The Gram row-sum bound yields cross-block norm $O(p)$. Consequently $\|K\|=O(p^{5/4})$. [Kunisky and Yu, Theorem 3.35 and equation (112)](https://arxiv.org/html/2211.02713#S4.SS7.SSS1)

For all odd primes the last cycle also has a direct $O(p^{3/2})$ bound. Embed a vector on unordered pairs into a matrix $Z$ supported at one chosen ordering per pair, preserving its Euclidean norm as a Frobenius norm. For fixed first output site $a$, let $D_a=\operatorname{diag}(S_{ac})_c$. The output at $(a,b)$ is the $b$-th diagonal entry of $S D_a Z D_a S^\top$. The sum of squared outputs over $b$ is at most $p^2\|Z\|_F^2$. Summing over $a$ and restricting to one ordering per output pair gives norm at most $p\sqrt{p+1}$. This gives the elementary range for either residue class.

## The stronger cross-cycle norm on both residue classes

Here is a projective reduction for the $O(p^{5/4})$ cross-cycle bound without the congruence restriction in the affine Paley graph theorem. On **ordered distinct** projective pairs let $P_{ab,cd}=S_{ac}S_{ad}S_{bc}S_{bd}$. Its nonzero spectrum is twice the unordered spectrum, since exchanging either ordering leaves all entries fixed. Every projectivity preserves $P$ because its determinant multiplier occurs four times and each change of a vertex representative occurs twice.

Every eigenspace of $P$ contains a nonzero vector fixed by all dilations. To see this, decompose the eigenspace under affine translations over $\mathbb C$. If a nontrivial additive character occurs, sum a vector in its character space over all dilations. These vectors belong to distinct orthogonal nontrivial character spaces, so their sum is nonzero. Otherwise all translations act trivially on the whole eigenspace. Projective invariance then makes their conjugates act trivially as well. Upper and lower unipotent matrices generate $\mathrm{SL}_2(\mathbb F_p)$ by elementary row operations. Its projective image is transitive on ordered distinct pairs, as it is transitive on the line and its infinity stabilizer contains every translation of finite sites. In this case the eigenspace consists of constants.

On finite ordered pairs, the dilation orbits are $(zi,z(i+1))$ for $i\in\mathbb F_p$, $z\ne0$. They all have size $p-1$. In the orthonormal basis of orbit indicators the compression has $(i,j)$ entry
$$
 \sum_{z\ne0}\chi((i-jz)(i-(j+1)z)((i+1)-jz)((i+1)-(j+1)z)).
$$
Including $z=0$ adds a matrix of norm at most $p$. After transposition the complete matrix has entries $T_{ij}=\sum_z g(iz-j)g((i+1)z-j)$, $g(t)=\chi(t(t-1))$. Compression of the blocks involving infinity still costs $O(p)$ by the cross-block Gram calculation (doubling the norm for ordered pairs suffices).

The Fourier argument for this smaller matrix works at every odd prime. Write $\mathrm{Kl}(u)=\sum_{t\ne0}e_p(t+u/t)$ with $\mathrm{Kl}(0)=-1$. The Fourier transform with positive sign satisfies $\widehat g(x)=e_p(x/2)\mathrm{Kl}((x/4)^2)$. For $x\ne0$ this follows by writing $u=2t-1$ and parametrizing $u^2-v^2=1$ by $u=(w+w^{-1})/2$. At $x=0$ both sides are $-1$. In the defining sum for $T$ the two arguments $a,b$ of $g$ range along $ib-(i+1)a=j$, with $z=b-a$. Additive orthogonality expresses $T$ as a row/column reindexing and unitary Fourier transform of the matrix with entries $p^{-1/2}\mathrm{Kl}(i^2x^2)\mathrm{Kl}((i+1)^2x^2)$, up to unit-modulus column phases before the Fourier transform. The map $x\mapsto x^2$ repeats each column at most twice. Thus $\|T\|\le(2/p)^{1/2}\|D\|$ for $D_{ix}=\mathrm{Kl}(i^2x)\mathrm{Kl}((i+1)^2 x)$. [Kunisky–Yu's Fourier factorization in Theorem 4.20](https://arxiv.org/html/2211.02713#S4.SS7.SSS2)

Remove the rows $i=0,-1$ from $D$ at cost $O(p)$ by the Weil bound $|\mathrm{Kl}(u)|\le2\sqrt p$ for $u\ne0$. For the remaining rows every scaling parameter is nonzero. The four-factor correlation of Fouvry, Kowalski and Michel bounds $(DD^\top)_{ij}$ by $O(p^{5/2})$ whenever one of $i^2,(i+1)^2,j^2,(j+1)^2$ occurs an odd number of times. Their result applies to every prime. The unnormalized $\mathrm{Kl}$ contributes a factor $\sqrt p$ for each of the four terms, and the single $x=0$ term costs one. For each $i$ there are at most five exceptional $j$, since every exception requires $j^2\in\{i^2,(i+1)^2\}$ or $j^2=(j+1)^2$. Their Gram entries are $O(p^3)$ by the pointwise Weil bound. The maximum absolute row sum is $O(p^{7/2})$. It follows that $\|D\|=O(p^{7/4})$ and $\|T\|=O(p^{5/4})$. The dilation reduction now bounds $P$, hence its affine principal submatrix and $K$, at **every** sufficiently large odd prime. [Fouvry–Kowalski–Michel, *A study in sums of products*, Corollary 3.3](https://people.math.ethz.ch/~kowalski/sums-of-products.pdf#page=18)

## Consequences for the relaxation

We have $u_4/u_2=O(k^2/p^2)$ and $u_3/u_2=O(k/p)$. The negative part that the perturbation can add, divided by $u_2$, is at most $O(k^2p^{-3/4}+k/p)$ at every odd prime. With the elementary norm estimate alone the cost is $O(k^2p^{-1/2}+k/p)$. An absolute sufficiently small $c>0$ makes this smaller than $(u_2-2u_3+u_4)/u_2$ throughout the stated ranges, on both grounds. This proves positivity on all squares of degree at most two.

All four-site assignment probabilities are also nonnegative. For disjoint sets of on-sites $T$ and off-sites $F$ with $|T|+|F|\le4$, the local mass is $\sum_{J\subseteq F}(-1)^{|J|}y_{T\cup J}$. When $F$ is empty all moments are nonnegative. Otherwise $|T|\le3$ and $y_T\ge(1-O(1/p))u_{|T|}$. The sum of all nonempty terms in absolute value is $O((k/p)u_{|T|})$, uniformly, since every higher moment is at most a constant times its true slice moment. These masses sum to one and give consistent marginals by Boolean inclusion–exclusion.

All the quartic mass of this functional lies in $H$. Choosing the singular or nonsingular blocks gives the two extreme objectives. For $p\equiv3\bmod4$ the nonsingular choice obstructs a lower bound near $1/4$. For $p\equiv1\bmod4$ the singular choice obstructs an upper bound near $1/4$. These are limitations on this degree-four certificate for prescribed sets. They give no actual $k$-set with an extreme count.

The [standard-library verifier](../../../scripts/probes/probe_paley_quartic_design_relaxation.py) computes the ternary determinants directly, verifies every size contraction and local Boolean assignment probability in its fixtures, and decides the pair-block PSD test by exact fraction-free elimination. It includes affine and projective examples at size five and an infeasible small-prime control. At primes 5, 7, 11 and 13 it also computes the characteristic polynomial of the dilation-orbit matrix and checks that it annihilates the full cross-cycle kernel on a coordinate vector. Projective transitivity supplies all other coordinate vectors. Run it with Python 3.

~~~sh
python3 -B scripts/probes/probe_paley_quartic_design_relaxation.py
~~~
