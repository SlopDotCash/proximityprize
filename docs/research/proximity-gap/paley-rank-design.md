# The distribution of singular four-site minors on a sampled domain

Let $p\ge7$ be prime, $v=p+1$, and use the projective Paley conference matrix $C$ on $\mathbb P^1(\mathbb F_p)$. Its entries are the quadratic characters of the determinants of the representatives $(x,1)$ and $(1,0)$, with zero diagonal. Call a four-site set a block if its principal minor is singular over $\mathbb F_3$. For a uniform $m$-subset $X$ of the $v$ sites, let $D(X)$ count its blocks. Put $e=\chi(-1)$ and
$$
\theta=\frac{p-2-3e}{4(p-2)} .
$$
Then for $4\le m\le v$,
$$
\mathbb E D(X)=\theta\binom m4,\qquad
\operatorname{Var}D(X)=\theta(1-\theta)\binom m4
                 \frac{\binom{v-m}4}{\binom{v-4}4}.
$$

**Completions of a triple.** The [four-site rank criterion](paley-four-site-rank.md) gives the following test. The rank condition on an ordered four-set is $\chi(\lambda)=\chi(1-\lambda)=e$, where $\lambda$ is its cross ratio. Indeed the three products of signs around the undirected four-cycles are $r,s,ers$ up to a permutation, with $r=\chi(\lambda)$ and $s=\chi(1-\lambda)$. They sum to $3e$ in the specified case and $-e$ otherwise. In the determinant the three pairs of transpositions each contribute 1 and the six directed four-cycles contribute minus twice that sum. Thus the two determinant values are $3-6e$ and $3+2e$. Only the first vanishes modulo three. Changing projective representatives or coordinates preserves the condition by diagonal sign conjugation and a common sign. Given three distinct sites, each $\lambda\ne0,1$ occurs for exactly one fourth site. Expanding $(1+e\chi(\lambda))(1+e\chi(1-\lambda))/4$ and summing on this range gives $(p-2-3e)/4$ completions, since the complete quadratic correlation is $-e$. Hence the blocks form a projective $3$-design. In particular every prescribed triple has the same completion density $\theta$.

**Fixed-size variance.** On four-sets write $w_I=\mathbf1_{I\,\mathrm{block}}-\theta$. Summing $w_I$ over the supersets of any triple gives zero. Double counting gives zero also over the supersets of each set of size at most two. For a fixed four-set $I$, let $c_t=\sum_{J:\,|J\cap I|=t}w_J$. For $0\le j<4$ we have $\sum_t\binom tj c_t=0$ by summing over the $j$-subsets of $I$, while $c_4=w_I$. Binomial inversion gives $c_t=(-1)^{4-t}\binom4t w_I$. Expanding the squared centered block count, a pair at intersection size $t$ is included with probability $(m)_{8-t}/(v)_{8-t}$. After factoring out the probability of selecting $I$, the alternating sum is the conditional probability that four prescribed sites outside $I$ are all omitted, by inclusion-exclusion. Summing $w_I^2$ over $I$ gives $\theta(1-\theta)\binom v4$, proving the formula.

## Every rectangle inside the same sampled domain

Let $E(X)=\operatorname{tr}((C_X C_X^t)^2)$ for the principal submatrix on $X$. The square of each two-row inner product expands into four-cycles. The nonzero terms with at least one repeated index contribute exactly $m(m-1)(2m-3)$. On four distinct sites each of the three undirected cycles occurs eight times. Hence
$$
 E(X)=m(m-1)(2m-3)+8e\left(4D(X)-\binom m4\right).
$$
In particular $\mathbb E E(X)=m(m-1)(2m-3)-24\binom m4/(p-2)$ and $\operatorname{Var}E(X)=1024\operatorname{Var}D(X)$. Chebyshev gives
$$
 \Pr(E(X)>3m^3)\le\frac{32}{3m^2}.
$$
Outside this exceptional fraction, **all** subsets $A,B\subseteq X$ satisfy
$$
 |S(A,B)|\le 3^{1/4}m^{3/4}\sqrt{|A||B|}.
$$
Indeed the fourth power of the largest singular value of $C_X$ is at most $E(X)$. The same event bounds all complex-weighted rectangles with the two Euclidean norms in place of the square roots of the sizes. For $|A|,|B|\ge c m$ with fixed $c>0$, the relative discrepancy is at most $3^{1/4}c^{-1}m^{-1/4}$. Thus both partners can be chosen after seeing one sampled set. The variance still permits exceptional prescribed sets.

The verifier forms the actual integer conference matrix including infinity, tests the four-site determinants modulo three, and accumulates block counts over all fixed-size slices. On selected domains it independently compares them with the matrix fourth moment. [Exact verifier](../../../scripts/probes/probe_paley_rank_design.py)
