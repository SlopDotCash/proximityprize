# Computing exact lists from syndrome flats

At length eight and rate one half, the worst closed list at three errors on a smooth evaluation coset has size **eight in characteristic three and seven in every other admissible characteristic**. This holds at every positive interleaving width. The proof below also gives the upper bound seven on every eight-point domain in characteristic different from three. The exceptional case changes the first failure for list budget seven.

## First failure on a smooth octagon

Let $q$ be a prime power with $8\mid q-1$, let $D$ be any multiplicative coset of the eighth roots of unity in $\mathbb F_q$, and set $Q=q^m$ for interleaving width $m\ge1$. A basis of $\mathbb F_Q$ over $\mathbb F_q$ identifies a column of $m$ symbols with one $\mathbb F_Q$ symbol. This takes the interleaved code to the degree-below-four evaluation code over $\mathbb F_Q$ and preserves the error sites. Rescaling the evaluation variable takes any such coset to $\mu_8$. Put $L=8$ in characteristic three and $L=7$ otherwise.

| Integer list budget $B=\lfloor q/2^{128}\rfloor$ | First bad error count | First bad relative radius |
|---|---:|---:|
| $B=0$ | 0 | 0 |
| $1\le B<L$ | 3 | $3/8$ |
| $L\le B<70$ | 4 | $1/2$ |
| $B\ge70$ | 5 | $5/8$ |

The table holds for every integer budget $0\le B\le q$ as well. At two errors the worst list is one by minimum distance five. At four errors each four agreeing sites determine a unique cubic, giving at most $\binom84=70$ words. The center $x^4$ attains all 70 via the distinct cubics $X^4-\prod_{a\in S}(X-a)$ for four-subsets $S$. At five errors, the zero center sees zero and the $56(Q-1)$ nonzero multiples of the monic cubics with three distinct domain roots. This exceeds $q$. The three-error value follows next.

### Why eight words force three-torsion

Use the four syndrome columns $v(x)=(1,x,x^2,x^3)^\mathsf T$ up to nonzero column multipliers. Two distinct errors representing one syndrome differ by a nonzero codeword, so the union of their supports has at least five sites. An error with at most one site excludes every other error of weight at most three. An error of weight two forces all others to be triples disjoint from it. Distinct triples share at most one site, so on the remaining six sites there are at most $\binom62/3=5$ such triples.

A list of at least eight therefore consists of triples. Each site occurs in at most three since pairs cannot repeat. Eight triples saturate the $8\cdot3$ incidences, so there are exactly eight, each site has degree three, and the pairs absent from every triple form a perfect matching. Write $i^*$ for the unmatched partner of $i$.

Fix the nonzero syndrome and pair it with coefficient vectors of binary cubics to get a nonzero linear functional $\ell$. A triple's columns span the hyperplane normal to its homogeneous cubic locator. Thus all eight triple locators vanish under $\ell$. Over the algebraic closure, choose a nonzero binary quadratic $H$ with $\ell(XH)=\ell(YH)=0$. Such an $H$ exists by dimension. The two-dimensional space $H\cdot\mathrm{span}(X,Y)$ lies in the kernel of $\ell$.

* If $H$ has distinct projective roots $A,B$, the annihilator of this space is the span of evaluations at $A,B$. Both evaluations have nonzero coefficients in $\ell$. Otherwise all eight locators would vanish at one common site, which contradicts degree three. Neither $A$ nor $B$ can be a domain site. If one were, all three triples through it would also contain the other, repeating a pair. In coordinates with $A=0$ and $B=\infty$, all eight labels are finite and nonzero. On a monic locator, the two evaluations give minus the product of its three roots and its leading coefficient one. Hence every triple has the same product.
* If $H$ has a double root, move it to $\infty$, so that $H$ is proportional to $Y^2$. The functional depends only on the $X^3$ and $X^2Y$ coefficients. The coefficient of the latter in the functional must be nonzero, since a single evaluation cannot occur. A locator having a simple root at $\infty$ has zero $X^3$ coefficient and nonzero $X^2Y$ coefficient. Therefore $\infty$ occurs in no triple and is no domain site. The monic locators now show that every triple has the same sum.

Write the resulting abelian group additively, even in the product case. Let $x$ denote a site's label, $x^*$ its partner's label, $t$ the common block sum, and $s$ the sum of all eight labels. Summing the three blocks through $x$ gives
$$
3t=s+2x-x^*.
$$
Apply the same identity to $x^*$ and eliminate its label. The result is $3x=3(3t-s)$ for all eight distinct labels. In the multiplicative group a cube fiber has at most three elements. In the additive group of a field of characteristic different from three the tripling map is injective. This proves the upper bounds. Lean verifies the double count and elimination for any finite incidence system with these pair multiplicities over any additive commutative group. [Formal three-torsion obstruction](../../../ArkLib/Research/ProximityGap/Frontier/OctagonTripleTorsion.lean)

### Attaining seven and eight

There are 56 five-subsets of $\mu_8$. Rotation by a generator multiplies each subset product by its fifth power, again a generator, so precisely seven subsets have each possible product. For one such fiber, let $P_S$ be its monic degree-five locator and fix a member $S_0$. The distinct polynomials $(P_{S_0}-P_S)/X$ have degree at most three since the locators have the same constant term. They agree with the center $P_{S_0}(x)/x$ at the five sites of $S$. This gives the seven-word lower bound in every admissible characteristic. [Formal common-product construction](../../../ArkLib/Research/ProximityGap/Frontier/PrescribedProductList.lean)

In characteristic three, $\mu_8=\mathbb F_9^\times$ in the ambient field. There are eight affine $\mathbb F_3$-lines in $\mathbb F_9$ avoiding the origin, two for each of four directions. Each of their triples sums to zero. Therefore its monic locator has $X^2$ coefficient zero and the syndrome $(0,0,1,0)^\mathsf T$ belongs to that triple's column span. It belongs to no two-column span because the top two entries of two distinct columns form an invertible Vandermonde matrix. The eight triples give eight distinct errors. Surjectivity of the syndrome map supplies a center. This proves attainment.

## General list histogram by matrix ranks

The following finite calculation applies to any linear $[n,k]$ code over $\mathbb F_q$, every number of errors $e$, and every positive width $m$. Set $r=n-k$ and choose a full-rank parity-check matrix $H$. For $J\subseteq[n]$ let $W_J$ be the span of its columns and let $r_J=\dim W_J$. A received center has an ordered syndrome tuple $z\in(\mathbb F_q^r)^m$. Every tuple belongs to exactly $Q^k$ centers.

Define
$$
A_j(z)=\sum_{|J|=j}Q^{j-r_J}\mathbf1_{z\in W_J^m}.
$$
The restriction of the syndrome map to errors supported inside $J$ has exactly $Q^{j-r_J}$ preimages for each tuple in its image. Hence an error of weight $i$ contributes $\binom{n-i}{j-i}$ times to $A_j$. If $N_i(z)$ counts errors of weight exactly $i$, the polynomial identity
$$
\sum_j A_j(z)u^j=\sum_i N_i(z)u^i(1+u)^{n-i}
$$
gives $\sum_iN_i(z)t^i=\sum_j A_j(z)t^j(1-t)^{n-j}$ after substituting $u=t/(1-t)$. Dividing by $1-t$ and taking the coefficient of $t^e$ gives the closed list for $e<n$,
$$
L_e(z)=\sum_{j=0}^e(-1)^{e-j}\binom{n-j-1}{e-j} A_j(z).
$$
At $e=n$ it is $Q^k$.

Form the finite set of distinct intersections of the $W_J$, including the full ambient space. Each tuple has a unique smallest flat $X$ containing every component. Its population is
$$
b_m(X)=Q^{\dim X}-\sum_{Y\subsetneq X}b_m(Y),
$$
where the sum runs over the intersection flats strictly inside $X$. For this stratum an indicator in $A_j$ equals one precisely when $X\subseteq W_J$. Adding $b_m(X)$ by the resulting list value counts all syndromes with that value. Zero-population strata are discarded, which matters over small fields. Multiplication by $Q^k$ gives the requested center counts. This uses dimensions and containments of the **represented intersection spaces**. Derived intersections can depend on column coordinates even for MDS codes with the same ordinary column matroid; the octagon gives a characteristic-sensitive example. Finite-field arrangement counts and higher-order MDS intersections give related general frameworks. [Athanasiadis](https://www.sciencedirect.com/science/article/pii/S0001870896900596) · [Brakensiek, Gopi and Makam](https://arxiv.org/abs/2206.05256)

For Reed–Solomon, take the columns $(1,x,\ldots,x^{r-1})^\mathsf T/\prod_{y\ne x}(x-y)$. These annihilate every polynomial of degree below $k$ by Lagrange interpolation at degree at most $n-2$. Dropping the nonzero multipliers preserves all column spans and kernel sizes. For $|J|<r$, $W_J$ is the intersection of the hyperplanes through $J$ that span $r-1$ columns. Extend $J$ to a basis and omit each extra basis member in turn. Their normals are coefficient vectors of the degree-$(r-1)$ locators. The probe constructs intersections by reducing these normals and records which hyperplanes contain each flat. With $h=\binom n{r-1}$ hyperplanes, at most $\sum_{i=0}^r\binom hi$ flats arise because independent normals suffice. This is a finite algorithm at every length, polynomial in $n$ for fixed redundancy, and too large at the designated $n=2^{30}$ and fixed positive rates. The capacity-side formulas can avoid constructing flats in their range. [Capacity-side profile](exact-list-profile-from-capacity.md)

## Two families at arbitrary length

**Even minimum distance.** Let $n-k+1=2e$ and $e\mid n$ on a multiplicative coset of size $n$. The largest list at $e$ errors, at every width, is exactly $n/e$. Two distinct errors representing one syndrome must have disjoint supports, each of size $e$, by the minimum-distance bound. Thus there are at most $n/e$. Partition the domain into cosets of $\mu_e$. On each coset place the weights $x^{-(e-1)}$ at its sites, using unscaled syndrome columns. Their power moments, indexed $j=0,\ldots,2e-2$, all vanish except for moment $e-1$, which equals the nonzero field element $e$. Indeed $x^{j-e+1}$ sums to zero over the coset unless $e\mid j-e+1$. Every coset therefore represents the same syndrome and all give distinct errors. Nonzero column multipliers only rescale the error magnitudes. The preceding radius has maximum list one by minimum distance. Consequently budgets $1\le B<n/e$ have first bad error count $e$.

**Redundancy three.** For every cyclic multiplicative coset of length $n\ge4$ and $k=n-3$, the maximum at two errors is $\lfloor n/2\rfloor$, including odd $n$. The same disjointness argument gives the upper bound. After rescaling to the subgroup generated by $g$, pair $x$ with $g/x$. For even $n$ the involution has no fixed point, and for odd $n$ it has one. The $\lfloor n/2\rfloor$ pair locators $X^2-(x+g/x)X+g$ all annihilate the syndrome $(1,0,-g)^\mathsf T$. It lies on no one-column span, since a multiple of $(1,x,x^2)^\mathsf T$ with first entry one and second zero requires $x=0$. This gives distinct errors for all the pairs. At three errors the monic center $X^k$ attains the interpolation upper bound $\binom n3$. At four errors the zero center contains zero and $(Q-1)\binom n4$ nonzero multiples of monic locators with $k-1$ roots. In particular the complete sponsor-budget threshold is 0 if $B=0$, 2 if $1\le B<\lfloor n/2\rfloor$, 3 if $\lfloor n/2\rfloor\le B<\binom n3$, and 4 if $\binom n3\le B<q$. These conclusions hold for all positive widths.

## Reproducible census

Run `python3 scripts/probes/probe_syndrome_flat_list.py` from the repository root. Direct enumeration checks each histogram bin on small scalar and interleaved cases. Over the Goldilocks prime $p=2^{64}-2^{32}+1$, the smooth octagon has respectively **1, 5184, 988, 56, 1** flats in dimensions zero through four. At widths one and two the three-error list spectrum is $\{0,1,2,3,4,5,7\}$. Exactly $8(Q-1)$ syndromes attain seven. The census checks that count without enumerating the $Q^8$ centers. The characteristic-sensitive theorem above is a written proof with a computational check on these cases. [Exact computation](../../../scripts/probes/probe_syndrome_flat_list.py)

The spectrum and maximizing count extend to **every characteristic $p>25{,}600{,}000{,}000$** admitting a smooth octagon in the chosen field, at every positive width. To see this, write the 56 locator normals with entries in $\mathbb Z[\zeta_8]$. Under every complex embedding the four coordinate magnitudes are bounded by $1,3,3,1$, so a row has Euclidean norm at most $\sqrt{20}$. Hadamard's bound gives absolute value at most 400 for every square minor of size at most four, at each of the four embeddings. A nonzero minor thus has nonzero integer norm of magnitude at most $400^4$. If that minor vanished after sending $\zeta_8$ to a primitive eighth root in characteristic $p$, its norm would be divisible by $p$. Above the displayed bound every minor has the same vanishing behavior as over the Goldilocks prime, which fixes the intersection lattice with its labeled supports.

For $e=3$, every term in the list formula uses at most three independent syndrome columns, so its value on each flat is independent of $Q$. Every positive-dimensional flat of dimension $d$ has population at least $Q^d-56Q^{d-1}$, by removing its intersections with the at most 56 hyperplanes that do not contain it. Over the Goldilocks prime this already exceeds $8(Q-1)$ for $d\ge2$, so every maximizing flat is a line. The zero stratum has list one and each line has $Q-1$ tuples with that minimal flat. The observed count therefore identifies exactly eight maximizing lines. The same argument preserves all attained list values and yields $8Q^4(Q-1)$ maximizing received centers throughout the stated characteristic range.
