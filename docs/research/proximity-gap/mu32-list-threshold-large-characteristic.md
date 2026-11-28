# The exact half-rate list threshold at length 32 and budget three

Let $F$ have characteristic $p>2^{128}$ and contain a subgroup $H$ of order 32. For the dimension-16 Reed–Solomon code on $H$, the largest list in a closed ball of nine Hamming errors is **three**, and some ball of ten errors contains **at least four** codewords. Both statements hold for every positive finite interleaving width. Consequently every such finite field with $\lfloor |F|/2^{128}\rfloor=3$ has last good integer radius 9, first bad integer radius 10 and operational supremum $5/16$. The prime $p=(3\cdot2^{48}+69)2^{80}+1$ gives a concrete instance. The nine-error list size also holds on the order-32 subgroups of the two named production fields. This argument uses length 32 throughout.

A [real-subfield norm estimate](mu32-quadratic-list-threshold.md) extends the nine- and ten-error conclusions to every characteristic above $2^{58}$, including all quadratic fields of budget three that contain this subgroup.

## Lifting a constant ratio of vanishers

Write $\zeta$ for a complex primitive 32nd root, $K=\mathbb Q(\zeta)$ and $L_A(X)=\prod_{a\in A}(X-\zeta^a)$ for a set of exponents. Let $A,B$ be disjoint with $|A|=|B|=d$. At two distinct sites $x,y$ outside them (writing the exponents for their corresponding roots), put
$$
U=L_A(x)L_B(y),\qquad V=L_B(x)L_A(y),\qquad Z=U-V .
$$
If $Z\ne0$ and a specialization in characteristic $p$ sends $Z$ to zero, then $p$ divides its nonzero integer norm. For odd $p$ it suffices to bound the odd part of this norm. Each factor of $U$ and $V$ is a root of unity times $1-\zeta^j$. At the unique prime over 2, normalized by $v(1-\zeta)=1$, we have $v(1-\zeta^j)=2^{v_2(j)}$. Indeed, $1-\zeta^j$ is conjugate to a lower-conductor uniformizer and its absolute norm is $2^{2^{v_2(j)}}$. Total ramification and residue degree one give $v_2(N_{K/\mathbb Q}(Z))=v(Z)$. Thus
$$
|N(Z)|_{\rm odd}\ \le\
\frac{2^{16}\prod_{\sigma\colon K\hookrightarrow\mathbb C}
      \max(|\sigma U|,|\sigma V|)}
     {2^{\min(v(U),v(V))}}. \tag{1}
$$

Translation and odd multiplication of exponents reduce $x,y$ to $0,s$, with $s=1,2,4,8$ for a nonantipodal pair. Conjugate complex embeddings make the same choice in the maximum. Enumerate the $2^8$ choices of $U$ or $V$ on the eight conjugate pairs. For each choice, the base-two logarithm of the product in (1), after subtracting $v(U)$, is a sum of per-site weights. Maximizing over the two orders of $A,B$ also covers subtraction of $v(V)$. At exponent $j$ the two conjugate embeddings indexed by $t,-t$ contribute either $\log_2|1-\zeta^{tj}|^2$ or $\log_2|1-\zeta^{t(j-s)}|^2$. The valuation charge for membership in $A$ is $2^{v_2(j)}$ and for membership in $B$ it is $2^{v_2(j-s)}$.

The verifier rounds every logarithm **upward** in units of $1/1024$. It encloses each squared chord via integer square roots using $D_j=2-2\cos(2\pi j/32)$, $D_{16-j}=4-D_j$ and $D_j=2-\sqrt{4-D_{2j}}$ for $j\le8$. For an upper endpoint $u/2^{40}$, the bit length of $u^{1024}-1$ gives $\lceil\log_2(u^{1024})\rceil$. A dynamic program considers each available site in turn. Its three choices are to skip the site, add it to $A$, or add it to $B$, with the numbers of sites assigned to each set indexing the table. Including the factor $2^{16}$ in (1), its rigorous upper bounds on $1024\log_2|N(Z)|_{\rm odd}$ are

| $d$ | $s=1$ | $s=2$ | $s=4$ | $s=8$ |
|---|---:|---:|---:|---:|
| 7 | 120222 | 116890 | 117580 | 110488 |
| 8 | 130246 | 125958 | 121680 | 117656 |
| 9 | 135522 | 134504 | 125780 | 124824 |

The entries for degrees seven and eight are strictly below $128\cdot1024$. Those for degree nine are below $133\cdot1024$. On any test set of at least three sites, its pairs other than the antipodal pairs form a connected graph. Therefore constancy of $L_A/L_B$ in the residue field implies constancy over $K$ on that same test set for $d=7,8$ when $p>2^{128}$, and for $d=9$ when $p>2^{133}$. The ratios are defined because all sites remain distinct. This argument lifts simultaneous ratios with an unknown common value. [Integer norm bounds and explicit lower construction](../../../scripts/probes/probe_mu32_ratio_norm.py)

## The list upper bound at nine errors

Four candidate codewords would have error sets of size at most nine whose pairwise unions have size at least seventeen by minimum distance. Each pair meets in at most one site. If one set has size eight, disjointness from the others and the total size force a triangle of three distinct pair overlaps among the other three. If all have size nine, the overlap multiplicity saves at least four sites. A site occurring in three sets forces at least two further overlaps with the fourth set and hence a triangle. With only double overlaps the four-vertex graph contains either a triangle or a four-cycle. Four sets sharing a single site can save only three sites.

In a triangle, remove the two triangle sites from each of its three error sets to get three disjoint seven-sets. Each pair difference of codeword polynomials is a scalar multiple of the vanisher on its fifteen forced equalities. Summing the three differences and cancelling their common vanisher produces a three-split pencil on those seven-sets. A constant ratio on one seven-set lifts by degree seven above. The characteristic-zero census excludes such a pencil.

In a pure four-cycle write $Q_i$ for the seven private errors at vertex $i$ and $s_{ij}$ for the site shared by adjacent vertices. Write $L_S$ for a site-set vanisher in the field. The four consecutive differences are scalars times $L_{Q_{i+2}}L_{Q_{i+3}}(X-s_{i+2,i+3})$. They sum to zero. At each $Q_j$ two terms survive, so the ratio for $Q_{j-1}\cup\{s_{j-2,j-1}\}$ and $Q_{j+1}\cup\{s_{j+1,j+2}\}$ is constant there. The degree-eight lift applies. For every such characteristic-zero ratio on seven sites, the exhaustive census found that both eight-sets are antipodally symmetric. Applying this at opposite vertices completes the same seven-set to an antipodally symmetric eight-set by adding two different single sites. Such a completion is unique when it exists. This contradiction excludes the four-cycle. The earlier census has 748 filtered inputs with no surviving degree-seven pencils and 4,077 cycle inputs yielding 33 normalized triples, all with symmetric outer sets. [Census and overlap argument](PROGRESS.md#2026-11-21--no-four-rate-half-codewords-within-nine-errors-on-the-32nd-roots-of-unity) · [Census verifier](../../../scripts/probes/probe_mu32_split_pencil_verify.py)

## Matching lower constructions

At nine errors, reserve seven of the eight sites of one fiber of $X^8$ and let $J$ vanish on them. Use the center $J(X)X^{16}$. For each choice of two of the three other fiber labels $a,b$, the polynomial $J(X)[X^{16}-(X^8-a)(X^8-b)]$ has degree at most 15. Each of the three choices gives a different codeword agreeing at 23 sites.

At ten errors take $H=\langle g\rangle$, $\omega=g^4$ and the four cubics $f_0,\ldots,f_3$ of the eight-fiber construction. At the eight values $\omega^j$ the respective matching classes of the center are $23,13,123,012,03,023,013,012$. Let $J$ be the degree-three vanisher on $1,g,g^4$, one site from each of fibers $0,1,4$ of $X^4$. Take the codewords $J(X)f_i(X^4)$ and the center given on each fiber by any member of its matching class. All four heads match at the three roots of $J$. Their agreement counts are $22,22,22,24$. The cubic equality identities hold over the integers at a primitive eighth root, so the construction applies in every stated characteristic. [Cubic polynomials and fiber classes](rate-half-eight-fiber-ceiling.md#the-quotient-polynomials)

An interleaved ball containing four distinct codewords would project to a scalar ball with four distinct codewords. Choose a linear combination of the rows outside the at most six hyperplanes that identify one of those pairs at a distinguishing coordinate. They cannot cover the coefficient space when $|F|>6$. All original agreements survive. Embedding the scalar construction in a row gives the interleaved lower bounds.

## A degree-nine consequence on these same sites

In characteristic zero the degree-nine three-fiber test also has a direct two-stage verification. In the binary tree of exponent parity classes keep, for each color $A$, the potential $v(L_B/L_C)$ at the sites of $A$. A pencil requires it to be constant on $A$, and likewise for the other colors. Within a child of the parity tree the contribution doubles when transported to its parent. The sibling contributes its number of $B$ sites minus its number of $C$ sites, because every cross-child difference has valuation one at that scale. This gives an exact recursion with a consistency check whenever both children contain the color. It yields 60,481,536 labeled colorings across 15 possible root states. Every such state has exactly one zero potential. Choosing that color first, ordering the other two, and fixing an omitted site leaves 1,575,040 unordered triples. Direct testing modulo 97 rejects all of them. The degree-nine norm bound thus excludes three full nonic fibers for **every characteristic above $2^{133}$**, including both named primes. The subgroup in this conclusion has order 32. The corresponding characteristic-zero maps would belong to the class of $N$-unital functions studied by Zhao, who classified levels up to four. [Dyadic enumeration](../../../scripts/probes/probe_mu32_nonic_fibers.py) · [Zhao, On N-Unital Functions](https://arxiv.org/abs/2103.15745)

## Dimension four at the same length

For the rate-eighth code on every smooth length-32 domain the first four-word list occurs at **20 errors**. This result holds in every field containing an element of order 32. For four distinct cubics and one received word, write $m_x$ for the number of agreements at site $x$. Since $m_x\le1+\binom{m_x}{2}$, the total number of agreements is at most $32+6\cdot3=50$. Each pair of cubics contributes at most three equalities. Four lists of thirteen agreements would require 52. Thus a ball at nineteen errors contains at most three codewords.

For the matching example let $z$ be primitive of order 32 and denote the cubic vanisher on the exponents in $A$ by $F_A$. Take
$$
A=\{0,1,2\},\qquad B=\{7,9,23\},\qquad C=\{11,25,27\}.
$$
Use the four polynomials
$$
0,\quad F_A,\quad F_B\frac{F_A(z^6)}{F_B(z^6)},\quad
F_C\frac{F_A(z^{14})}{F_C(z^{14})}.
$$
Both denominators are products of differences of distinct sites. For the pairs $01,02,03,12,13,23$, respectively, the following disjoint exponent sets give equal values:
$$
A,\quad B,\quad C,\quad \{6,20\},\quad\{14,28\},\quad\{13,17,21\}.
$$
The verifier checks each equality, after clearing denominators, in $\mathbb Z[z]/(z^{16}+1)$. They specialize in any field containing the primitive root. Set the center to the common value at these sixteen sites. The four words have secured 9, 7, 8 and 8 agreements. On the other sixteen sites assign respectively 3, 5, 4 and 4 further agreements. Each of the four distinct polynomials now agrees at twelve sites. The same projection argument gives the threshold at all positive interleaving widths. At budget three the last good integer radius is 19 and the operational supremum is $20/32=5/8$. [Integral equality certificate](../../../scripts/probes/probe_mu32_four_cubics.py)
