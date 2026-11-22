# An arbitrary prescribed Paley partner for every arc of a typical torus generator

Fix $0<\epsilon<1$ and an arbitrary set $Y$ of $n\ge p^\epsilon$ sites in the regular orbit of a split or nonsplit maximal torus $T\subseteq\mathrm{PGL}_2(\mathbb F_p)$. Its order is $m=p\pm1$. The set $Y$ can depend on the prime and the torus and is fixed before sampling a generator. For each integer $r\ge\lceil4/\epsilon\rceil$ and $0<\delta<\epsilon/(4r)$, all but a fraction
$$
 O_r\big(p^{-\epsilon/2+2r\delta+o(1)}\big)
$$
of generators $g$ satisfy the following at every sufficiently large odd prime. For **every** $p^\epsilon\le H\le m$ and **every** $H$-term consecutive-power arc $Z=(g^jx)_{0\le j<H}$ in the regular orbit, the projective Paley matrix from $Y$ to $Z$ has operator norm at most $\sqrt{2nH}\,p^{-\delta}$.

The good-generator set may depend on $Y$. At a good generator one may choose the length, starting point, subsets on both sides, and vertex weights after inspection. For $A\subseteq Y$, $B\subseteq Z$, arbitrary weights of modulus at most one give absolute discrepancy at most $\sqrt{2nH|A||B|}\,p^{-\delta}$. In particular this saves a power relative to $|A||B|$ for subsets of fixed positive densities. Transposition gives the same assertion with the arc on the row side. The unrestricted Paley conjecture allows a second arbitrary prescribed set at every placement. [Projective signs and Paley discrepancy](paley-four-site-rank.md#the-signed-four-cycle-controls-a-prescribed-rectangle)

In the split case one can also admit either or both torus-fixed sites as rows. Removing them leaves at least $n-2$ regular sites, and the same proof applies with $n-2\ge p^\epsilon/2$ for large $p$. Their two restored rows have norm at most $\sqrt{2H}$, adding at most $\sqrt{2/n}$ to the normalized bound.

## A matrix inequality for repeated column labels

Let $v_j$ be the columns of an $n$-by-$L$ matrix with $\|v_j\|_2^2\le n$. Write $Q_j=v_jv_j^*$, $S=\sum_j Q_j$, $R=\|S\|/(nL)$ and
$$
 D_r=\sum_{j_1,\ldots,j_r\ \mathrm{distinct}}\mathrm{tr}(Q_{j_1}\cdots Q_{j_r}).
$$
The sum is real by reversal. We claim that for $r\ge2$
$$
 R^r\le\frac{2D_r}{(nL)^r}+O_r(L^{-r/2}).                       \tag{1}
$$
Individual summands may be negative. For a partition $\pi$ of the $r$ positions into $s$ blocks, let $W_\pi$ be the sum of their ordered matrix products with labels equal inside each block. Distinct blocks are allowed to choose equal labels. Then
$$
 |\mathrm{tr}\,W_\pi|\le n^{r-s}\|S\|^{s-1}\mathrm{tr}\,S.       \tag{2}
$$
Fix a label $j_0$ of one block and put its first $Q_{j_0}$ first by cyclicity of trace. For the remaining operator product, scan the other positions in multiplication order, storing each active repeated block's label on its own $\ell^2(\{1,\ldots,L\})$ factor. On first opening a repeated block the map $u\mapsto(Q_j u)_j$ has squared norm $\|\sum_j Q_j^2\|\le n\|S\|$. Closing it is the adjoint after permuting the stored factors. At an intermediate occurrence, apply the block-diagonal operator with entries $Q_j$, of norm at most $n$. An independently chosen singleton supplies $S$. Previously fixed $j_0$ positions have norm at most $n$. Inserting identities on other label factors leaves these bounds unchanged. Contracting all stored factors sums every permissible label assignment. A free block of size $b$ therefore costs at most $n^{b-1}\|S\|$, and the remaining positions of the fixed block cost $n$ each. The resulting operator has norm at most $n^{r-s}\|S\|^{s-1}$ uniformly in $j_0$. Apply $|\mathrm{tr}(Q_{j_0}U)|\le\mathrm{tr}(Q_{j_0})\|U\|$, and sum over $j_0$ to obtain (2).

By inclusion-exclusion on equalities of labels, $D_r$ equals $\mathrm{tr}\,S^r$ plus a linear combination, with coefficients depending only on $r$, of traces (2) with $s<r$. Use $\mathrm{tr}\,S\le nL$ and $\|S\|^r\le\mathrm{tr}\,S^r$. After division by $(nL)^r$, the error is at most $C_r\sum_{k=1}^{r-1}L^{-k}R^{r-k-1}$, where $k=r-s$. Young's inequality allows any fixed positive fraction of $R^r$ to absorb each term at cost $O_r(L^{-kr/(k+1)})$. For $k=r-1$ the term is already constant in $R$. Since $k/(k+1)\ge 1/2$, absorbing a total of $R^r/2$ proves (1).

## The two-parameter average with fixed rows

Choose a reference site $x$ of the regular orbit. For $A,C\in T$, let $v_j$ be the column of brackets from the $n$ fixed rows to $CA^jx$, $0\le j<L$. Keep all labels even if $A$ is a nongenerator. Take the quadratic character of each determinant, extended by zero. Rescaling projective lifts leaves the trace expressions unchanged. Assume $2L<p$. We will use (1) through
$$
 \frac1{m^2}\sum_{A,C}R^r\ll_r n^{1-r}+L^{-r/2}+L/p.             \tag{3}
$$

Expand $D_r$ in closed walks of row and column labels. Each of its $r$ column labels occurs at exactly one column vertex of the walk. It supplies two brackets, one for each adjacent row. If all cells of the matrix occur an even number of times, both adjacent rows must be the same at each column. Hence all $r$ rows coincide. These at most $nL^r$ walks contribute at most $n^{1-r}$ to the normalized average.

For any other walk use the two rational parameter planes of the torus to sum the bracket product over $(A,C)$. In the eigenline coordinates $t=a_1/a_2$, $y=c_1/c_2$, associate to each fixed row $u$ the unique torus translate of $x$ taking it to $u$, of eigenratio $\lambda_u$. The graph for cell $(u,j)$ is $y=\lambda_u t^{-j}$. Around the walk the product of brackets differs geometrically from the product of these graph equations by squares. Indeed the factors from each fixed row occur twice per visit, the homogeneous factors in the $C$ coordinates occur $2r$ times, and both the $a_2$ and the extra $t^j$ powers are even in total since each column supplies two edges. Over $\mathbb F_p$ the arithmetic cover is defined by the original bracket section of even bidegree, preserving its twist. The graph itself is defined over $\mathbb F_p$ by the torus product map $C=(u/x)A^{-j}$.

Remove even-multiplicity factors. For every occupied slope $-j$ there are now either zero sections or two sections with distinct constants $\lambda_u$. The latter occurs wherever adjacent rows differ, so the branch set is nonempty. The surface proof for monomial sections still gives a character sum $O_r(Lp)$, as follows. At the finite nonzero parameter values, sections of the same slope stay apart. Intersections between different slopes are transverse, since their slope difference is nonzero modulo $p$, and there are $O_r(L)$ collision points. On the chains over $t=0,\infty$, each vertical line receives at most two horizontal branch marks at distinct nonzero coordinates. The multiplicity along the line of valuation $h$ at $0$ is $\sum_d b_d\min(h,d)$ up to an even integer, where $b_d$ is the number of surviving sections of slope $d$. Every $b_d$ is even. The same holds at infinity with opposite slopes. Therefore all vertical lines in these chains are unbranched. Each preimage has at most two branch points, so its components are rational. The ramification section, Albanese and Betti-number argument applies with the same $O_r(L)$ total blowups. There are at most $2r$ original graphs to restore when comparing with the arithmetic character sum. This proves the claim uniformly in the fixed rows and, after division by $(nL)^r$ and use of (1), proves (3). [Resolution, rational fiber and finite-field surface estimate](paley-torus-uniform-arcs.md#a-surface-estimate-for-the-nonpaired-walks)

## Every arc and length

Use all windows of length $L$ with integer starts in $[-L+1,H-1]$ on the column side. Each target column has $L$ representations; selecting those integer representations still works when the sites wrap around the orbit. Concatenate their matrices and embed a unit vector on the long arc by copying its entries with scale $1/\sqrt L$ on their representations. The resulting product equals $\sqrt L$ times the long-arc product. The squared norm of the concatenation is at most the sum of the squared block norms. There are $s=H+L-1<2H$ blocks, and for a generator at most two starts give any one relative rotation because $H\le m$. Jensen's inequality therefore yields
$$
 \sup_{c_0\in T}\left(\frac{\|P^H_{Y,c_0}\|}{\sqrt{nH}}\right)^{2r}
 \le\frac{2^{r+1}}{H}\sum_{c\in T}R_{g,c}^r.
$$
Summing over generators and using nonnegativity to include all $A\in T$ in (3) costs $m^2/(H\varphi(m))\ll p^{1+o(1)}/H$. Set $L=\lfloor\sqrt H\rfloor$. For $n,H\ge p^\epsilon$ and $r\epsilon\ge4$ the resulting mean bound is
$$
 \ll_r p^{o(1)}\left(\frac{p n^{1-r}}H+
          pH^{-1-r/4}+H^{-1/2}\right)\ll_r p^{-\epsilon/2+o(1)} .
$$
Markov's inequality at the dyadic ceilings of the lengths, using $m$ as the last ceiling, gives the stated exceptional fraction. Restricting a passing block of length at most $2H$ gives the factor $\sqrt2$. [Integer window coverage and endpoints](paley-torus-uniform-arcs.md#sliding-windows-and-every-relative-start)

## One generator for every row set against an unweighted split arc

In the standard affine split chart, fix $0<\epsilon<1$, an integer $r\ge\lceil2/\epsilon\rceil$, and $0<\delta<\epsilon/(4r)$. All but a fraction $O_r(p^{-\epsilon/2+2r\delta+o(1)})$ of primitive roots $g\in\mathbb F_p^\times$ work **simultaneously for every row set** $A\subseteq\mathbb F_p$ with $|A|\ge p^\epsilon$, every choice of $|\alpha_x|\le1$, and every whole arc $b,bg,\ldots,bg^{H-1}$ with $b\ne0$, $p^\epsilon\le H\le p-1$. The relative discrepancy satisfies
$$
 \frac{1}{|A|H}\left|\sum_{x\in A}\alpha_x\sum_{j=0}^{H-1}\chi(x-bg^j)\right|
 \le p^{-\delta}+p^{-\epsilon/2}.
$$
Here $A$, the row weights and the arc can all be selected after seeing $g$. Column weights in this statement are constant over the whole arc.

Put $L=\lfloor p^{\epsilon/2}\rfloor$, $S_g(x)=\sum_{j<L}\chi(x-g^j)$ with $0\le j<L$, and $E_g=\sum_{x\in\mathbb F_p}|S_g(x)/L|^{2r}$. Expand the moment first over every $t\in\mathbb F_p^\times$. At most $(2r-1)!!L^r$ exponent tuples have all multiplicities even, each contributing at most $p(p-1)$. For any other tuple the arithmetic character is that of the actual polynomial $\prod_{a=1}^{2r}(x-t^{j_a})$. Its odd-multiplicity graphs $x=t^j$ are distinct, one per slope, and their number is even and positive. The two-parameter surface bound gives $O_r(Lp)$ for its sum over $t\ne0$, $x\in\mathbb F_p$. To place this polynomial in a square line bundle, homogenize its $t$-degree to the next even integer if necessary. This may add a vertical branch at $t=\infty$. The rational-chain proof above $t=0$ still applies with one horizontal mark per slope; the resolution at infinity already allows odd vertical components. Keeping $x=0$ changes a sum restricted to $x\ne0$ by at most $p-1$. [Surface estimate and boundary accounting](paley-torus-uniform-arcs.md#a-surface-estimate-for-the-nonpaired-walks)

Each $E_t$ is nonnegative. Retaining just primitive roots and dividing by $\varphi(p-1)$ gives $\mathbb E_g E_g\ll_r p^{o(1)}(p L^{-r}+L)$. Markov's inequality shows $E_g\le p^{\epsilon-2r\delta}$ outside the stated exceptional fraction. At a passing generator, Hölder bounds any $L$-block sum by $L|A|^{1-1/(2r)} E_g^{1/(2r)}\le L|A|p^{-\delta}$. Every block start $b$ gives the same moment by $\sum_{j<L}\chi(x-bg^j)=\chi(b)S_g(x/b)$. Partition any length into full blocks and a remainder of size less than $L$. This proves the result for all lengths and starts, including wrapped arcs.

For disjoint arcs of total size $H$ with $k$ components the same relative estimate is $p^{-\delta}+kL/H$. For a single arc with column weights $\beta_j$, summation by parts over prefixes bounds its relative discrepancy by
$$
 (p^{-\delta}+L/H)
 \left(|\beta_{H-1}|+\sum_{j=0}^{H-2}|\beta_{j+1}-\beta_j|\right).
$$
Indeed each length-$s$ prefix has absolute sum at most $|A|(s p^{-\delta}+L)$, even for $s<L$.

## All linear phases and all row sets on the same split arcs

Write $e(u)=\exp(2\pi i u)$. In the same standard affine chart take $r\ge\lceil3/\epsilon\rceil$ and $0<\delta<\epsilon/(6r)$. Outside a fraction $O_r(p^{-\epsilon/3+2r\delta+o(1)})$ of primitive roots, for all $|A|,H\ge p^\epsilon$, $H\le p-1$, all $b\ne0$, all complex row weights $|\alpha_x|\le1$, and **every real $\theta$ simultaneously**, one has
$$
 \frac1{|A|H}\left|\sum_{x\in A}\alpha_x\sum_{j=0}^{H-1}
                  e(j\theta)\chi(x-bg^j)\right|
 \le 2p^{-\delta}+p^{-2\epsilon/3}.                               \tag{4}
$$

Take $L=\lfloor p^{\epsilon/3}\rfloor$ and let $E_{g,\theta}$ be the preceding $2r$th row moment with $e(j\theta)$ inserted in its length-$L$ sum. In the expansion of the absolute $2r$th power, the first $r$ selected exponents contribute phases and the last $r$ contribute their conjugates. The resulting coefficient has modulus one and is independent of both field parameters. The same signed surface estimate applies term by term, including tuples of odd total $t$-degree, and gives $\mathbb E_g E_{g,\theta}\ll_r p^{o(1)}(pL^{-r}+L)$ uniformly in $\theta$. Markov's inequality at the $M=4L$ phases $k/M$ simultaneously bounds $E_{g,k/M}\le p^{\epsilon-2r\delta}$ outside the stated fraction. This uses $pL^{-r}=O_r(1)$. At a passing generator, Hölder and the change $x\mapsto x/b$ bound every length-$L$ weighted row sum by $L|A|p^{-\delta}$ at every mesh phase.

For completeness, the mesh bounds every real phase with a factor of two. Put $F_a(u)=a^{-1}|\sum_{j=0}^{a-1}e(ju)|^2$ and $V=(3F_{3L}-F_L)/2$. Its Fourier coefficients equal one at $|h|\le L$ and vanish at $|h|\ge3L$. For every polynomial $P(u)=\sum_{j=0}^{L-1}c_je(ju)$, discrete orthogonality gives
$$
 P(u)=\frac1M\sum_{k=0}^{M-1}P(k/M)V(u-k/M).
$$
Indeed $h\equiv j\pmod M$ in the indicated supports forces $h=j$. Each nonnegative $F_a$ used here has grid mean one at every shift since $a<M$, so the grid mean of $|V|$ is at most two. Apply this to the polynomial of each chosen row set and row weights. When a length-$H$ arc is split into full $L$-blocks the shift of its phase contributes only a unit scalar to each block. The leftover length is less than $L$, uniformly in $b,H$ and $\theta$; thus it contributes at most $L/H\le p^{-2\epsilon/3}$ to (4). No sampling of the lengths is required.

More generally, if $\beta_j=\int e(j\theta)\,d\nu(\theta)$ on the $H$ arc labels for a finite complex measure on $\mathbb R/\mathbb Z$, the right side of (4) is multiplied by its total variation $\|\nu\|$. This includes weights with bounded sum of absolute Fourier coefficients, and gives the single-phase bound for alternating signs irrespective of $H$.

The companion verifier tests the constrained traces (2) on signed matrices, the arithmetic walk factorization and the two-mark branch condition on both torus types. For the affine split result it also tests the moment expansions, Fourier interpolation off the mesh, and post hoc row choices for wrapped arcs. [Finite verifier](../../../scripts/probes/probe_paley_arbitrary_partner_arcs.py)

```sh
python3 -B scripts/probes/probe_paley_arbitrary_partner_arcs.py
```
