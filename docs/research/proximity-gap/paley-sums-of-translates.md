# Prescribed Paley rectangles on sums of translates

Let $X,Y,T,U$ be nonempty subsets of $\mathbb F_p$ at an odd prime. Write $x=|X|$, $y=|Y|$, $t=|T|$, $u=|U|$ and $n=\min(x,y)$. Count the representations $m(s)=\#\{(v,w)\in T\times U:v-w=s\}$ and put
$$
 R=\frac{(tu)^2}{\sum_s m(s)^2}.
$$
Let $P$ be the matrix $(\chi(a-b))$ on the **prescribed** sets $A=X+T$, $B=Y+U$. For every integer $r\ge2$,
$$
 \left(\frac{\|P\|_{2\to2}}{\sqrt{xytu}}\right)^{2r}
 \le 2^r\frac pR\left((2r-1)!!\, n^{1-r}+(2r-1)p^{-1/2}\right). \tag{1}
$$
In particular $n\ge p^\epsilon$ and $R\ge p^{1/2+\kappa}$ give a power saving relative to $\sqrt{xytu}$, at every prescribed placement. Take $r\ge1+1/(2\epsilon)$ for a saving exponent $\kappa/(2r)$. If the two addition maps have bounded average multiplicity, this is also a saving relative to $\sqrt{|A||B|}$. All subsets and vertex weights are allowed by the operator norm. A common projective change preserves the same bound by sign conjugation. The estimate depends on the number of representations of *differences between the shifts*. The sets $X,Y$ can have arbitrary additive energy. [Sign change under projectivities](paley-four-site-rank.md)

## Shifted matrix moments

Put $M_s=(\chi(x_i-y_j+s))_{x_i\in X,\, y_j\in Y}$ and $L_s=\|M_s\|_{2\to2}/\sqrt{xy}$. First suppose both sides have size at most $n$. The trace of $(M_s M_s^*)^r$ is the sum over closed alternating walks
$$
 x_1,y_1,x_2,y_2,\ldots,x_r,y_r,x_1
$$
of the product of the $2r$ edge entries. Label each edge by its row coordinate minus its column coordinate, irrespective of traversal direction. A walk whose labels all have even multiplicity permits a pairing of the $2r$ positions with equal labels. For each fixed pairing choose the initial row in at most $n$ ways. On reaching the first edge of a pair there are at most $n$ choices for the next vertex. On reaching its partner the stored difference determines the next vertex uniquely. The final closing constraint only reduces this count. Thus there are at most $(2r-1)!!\,n^{r+1}$ such walks, and the absolute sum over $s$ for each is at most $p$.

For every other walk the polynomial in $s$ has a root of odd multiplicity. Weil's bound gives at most $(2r-1)\sqrt p$ for the absolute complete character sum. There are at most $n^{2r}$ walks altogether. The trace dominates $\|M_s\|^{2r}$, since it sums the $2r$-th powers of the singular values. [Weil estimate and distinct-root convention, Theorem A.1](https://link.springer.com/article/10.1007/s40879-021-00521-5)

For unequal sizes split the larger side, of size $N$, into $k=\lceil N/n\rceil$ pieces of size at most $n$. For their matrices $M_{s,j}$, stacking the rows gives $\|M_s\|^2\le\sum_j\|M_{s,j}\|^2$ (transpose if the columns are split). The $r$-th power is at most $k^{r-1}\sum_j\|M_{s,j}\|^{2r}$. Since $kn\le2N$ the preceding count gives
$$
 \frac1p\sum_s L_s^{2r}\le 2^r\big((2r-1)!!\,n^{1-r}+(2r-1)p^{-1/2}\big). \tag{2}
$$
In particular for any prescribed pair of shapes of polynomial size, outside a power-saving proportion of relative translations there is a power saving simultaneously for every dense subrectangle, including after independent sign choices on both sides. Estimate (1) uses many shifts to obtain a result at an individual prescribed placement.

## From a distribution of shifts to one pair of sets

Initially label rows by $T\times X$ and columns by $U\times Y$, keeping every representation. A $(v,w)$ block has norm $\sqrt{xy}L_{v-w}$. The squared norm of a block matrix is at most the sum of squared block norms: bound each block pairing by its norm times the two vector norms, then apply Cauchy–Schwarz over the block indices. Choosing one representative for each site in $A,B$ gives $P$ as a compression of the labelled matrix. Hence its squared norm divided by $xytu$ is at most the mean of $L_{v-w}^2$ over $T\times U$. Jensen with exponent $r/2\ge1$ and Cauchy–Schwarz give
$$
 \left(\frac{\|P\|^2}{xytu}\right)^{r/2}
 \le \frac1{tu}\sum_s m(s)L_s^r
 \le \left(\frac1R\sum_s L_s^{2r}\right)^{1/2}.
$$
Square this inequality and apply (2).

Overlapping translates also give a weighted version. For $a\in A$ let $h_A(a)$ count its representations in $X+T$ and define $h_B$ on $B$ likewise. Lift a weight $f(a)$ to the constant $f(a)/h_A(a)$ on its representation fiber. Its squared norm becomes $\sum_a |f(a)|^2/h_A(a)$, and the labelled pairing of the two lifted vectors equals the original pairing exactly. Thus the bound on the labelled operator multiplies
$$
 \left(\sum_{a\in A}\frac{|f(a)|^2}{h_A(a)}
       \sum_{b\in B}\frac{|g(b)|^2}{h_B(b)}\right)^{1/2}.
$$
For prescribed subdomains with multiplicities at least $k,l$, the unnormalized operator ceiling gains a factor $1/\sqrt{kl}$.

For example take $T=U$ additive Sidon of size $t$, meaning each nonzero difference occurs at most once. Then $R=t^4/(2t^2-t)\ge t^2/2$. With $X=Y$ of polynomial size and $t\ge p^{1/4+\gamma}$, (1) controls the Paley operator on $X+T$. For bounded average multiplicity, putting $N=|X+T|$ gives $\|P\|\ll Np^{-\delta}$ for some $\delta>0$. For any subset $Z$ of size $z\ge4$ the singular four-site fraction differs from $1/4$ by $O(1/z+N^2p^{-2\delta}/z^2)$ by the principal four-cycle identity. [Four-site rank normalization](paley-four-site-rank.md)

Here is an explicit family with unbounded doubling on its original chart. Fix $\gamma,\epsilon>0$ with $2\gamma+\epsilon<1/2$. Take a prime $\ell\asymp p^{1/4+\gamma}$, $h=\lceil p^\epsilon\rceil$ and
$$
 D=\{2\ell j+(j^2\bmod\ell):0\le j<\ell\},\qquad
 X=[0,h),\qquad T=2hD.
$$
Use representatives in $[0,\ell)$ for the residues. An equality between two nonzero differences in $D$ first identifies the index differences as integers: the two residue differences differ by strictly less than $2\ell$. Reducing modulo $\ell$ then identifies the index sums, hence the ordered pairs since $\ell$ is odd. For large $p$, all sums of two elements of $X+T$ lie below $p$ since $h\ell^2=o(p)$. The translates of $X$ are disjoint and the distinct sums in $T+T$ support disjoint translates of $X+X$. Thus $N=h\ell$, $|(X+T)+(X+T)|=(2h-1)\ell(\ell+1)/2$, and all dense subsets of this deterministic $p^{1/4+\gamma+\epsilon}$-scale family satisfy the rank and discrepancy estimates. The unrestricted problem requires bounds also for sets with no such representation.

The square-root threshold for $R$ has an obstruction in extension fields. Put $q=\ell^4$ for an odd prime $\ell$ and identify the additive group of its quadratic subfield $L=\mathbb F_{\ell^2}$ with $\mathbb F_\ell^2$. In these coordinates take $T=U=\{(j,j^2):j\in\mathbb F_\ell\}$ and $X=Y=\{(0,k):k\in\mathbb F_\ell\}$. Each nonzero ordered difference in $T$ determines $j-j'$ and then $j+j'$, so $T$ is Sidon. Every point of $L=X+T$ has a unique representation and $R=\ell^4/(2\ell^2-\ell)\sim\sqrt q/2$. Every element of $L^\times$ is a square in $\mathbb F_q$, so the relative discrepancy on $L\times L$ tends to one. Both template and shift sets have size $q^{1/4}$ in this example.

The [exact finite verifier](../../../scripts/probes/probe_paley_translate_moments.py) compares traces with sums over closed walks, checks the even-label counts, and tests the shift weights and the Sidon construction.
