# Half-rate successor witnesses require at least 23,170 polynomial degrees

At the first named half-rate MCA candidate, **268,435,457 errors**, any witnessing punctured list of four scalar polynomial heads has **at least 23,170 distinct monomial degrees in its differences**, even after removing their common polynomial factor. At least three of the six individual pair differences have at least **16,384 terms** after division. The four affine-target error locators from the same witness require at least **336 degrees** in their combined support. The assertions use the actual order-$2^{30}$ subgroup over the named finite field. [MCA equivalence, exact punctured profiles and affine-target locators](first-prime-punctured-four-list.md)

## Products of disjoint pairs

Put $n=2^{30}=4h$ and let $D_0,\ldots,D_3$ be the distinct punctured heads of degrees at most $2h-2$. Away from the puncture $a$, let $m_r$ count sites where exactly $r$ heads err. The possibilities for $(m_0,m_2,m_3)$ are $(0,5,0)$, $(1,6,0)$ and $(0,3,1)$, always with $m_4=0$. Each pair of error sets has at most one common site, and some pair meets. Every such pair has exactly $2h-2$ shared correct sites, exhausting the roots of the difference of its two heads.

Let $J$ be the monic gcd of the three differences from $D_0$. It divides a difference with the preceding complete set of simple roots. Hence every root of $J$ is a simple ordinary grid site where all four heads agree. Since $m_4=0$, all four must be correct there. Thus $\deg J\le m_0\le1$. Write $U_i=(D_i-D_0)/J$.

For any partition into two pairs $ij,kl$ the nonzero polynomial
\[
                    F=(U_i-U_j)(U_k-U_l)
\]
has degree at most $n-4$. It consequently has a nonzero evaluation on the full grid. At every site with exactly one error, at least one matched pair consists of two correct heads, so $F$ vanishes. At an all-correct site the same is true before division by $J$; count this site as a possible exception afterwards. In the profiles with $m_0=0$ there are at most $1+m_2+m_3\le6$ exceptional sites including the puncture. In the six-overlap profile all six pairs of error sets meet at distinct sites. At two of those sites the correct pair is one of $ij,kl$, forcing $F=0$. This leaves at most four double-error sites, the puncture and the possible root of $J$. Thus in every profile $F$ has **at most six nonzero evaluations**. The same bound holds before removing the common factor.

## A dyadic uncertainty bound in the actual field

On a coset of a cyclic grid of order $2^k$, let $T$ be the nonempty support of a function with nonzero values $w_x$ there. Among the moments $M_j=\sum_{x\in T} w_x x^j$ for $0\le j<2^k$, at least $2^k/2^b$ are nonzero whenever $|T|<2^{b+1}$. This applies in any field admitting the grid. To see this, split the coset into its two parity classes, on which $x^{2^{k-1}}$ has distinct opposite values. If only one class is occupied, each smaller-grid moment gives two nonzero moments upstairs whenever it is nonzero downstairs. If both are occupied, the smaller class has size below $2^b$. Its moments are recoverable from the pair $M_j,M_{j+2^{k-1}}$ by the invertible two-by-two matrix for the two distinct class values. Each nonzero smaller-class moment therefore gives at least one nonzero moment upstairs. Induction proves the claim, with a single nonzero weight at grid size one. [Lean proof in arbitrary fields and production specialization](../../../ArkLib/Research/ProximityGap/Frontier/DyadicMomentSupport.lean)

Apply this to the nonzero evaluations of $F$ on the inverse grid, with $b=2$. By finite Fourier inversion, its cyclic coefficient at $j$ is $n^{-1}\sum_{x\in H}F(x)x^{-j}$. Since $\deg F<n$, these are the actual coefficients. Consequently **at least $n/4=268,435,456$ coefficients of each matching product are nonzero**. Moreover any arithmetic progression of six frequency indices with odd step contains a nonzero coefficient: six consecutive zeros in such a progression would give a square Vandermonde system on the at most six distinct inverse sites raised to that odd power, forcing all weights to vanish.

Let $S$ be the union of the exponent sets of $U_i$, and let $s=|S|$. Every nonzero coefficient of a matching product has its degree in $S+S$, which has size at most $s(s+1)/2$. The two neighboring integer values give $23169\cdot23170/2<n/4\le23170\cdot23171/2$. Also the product of the term counts of $U_i-U_j$ and $U_k-U_l$ is at least $n/4=16384^2$. Each of the three complementary matchings therefore supplies a distinct difference with at least 16,384 terms.

## The error locators

For the four full locators $L_i=A+\ell_i B$ with affine $\ell_i$, put $G=\prod_i L_i$. Its evaluations are nonzero precisely at the puncture and the $m_0$ all-correct ordinary sites. Regardless of the degree, reducing $G$ modulo $X^n-1$ gives coefficients equal to its inverse Fourier transform. If there is only one site, every coefficient is nonzero. If there are two sites $a,b$ and $t$ is the order of $a/b$, a zero coefficient requires $(a/b)^j=-G(a)/G(b)$, so at most $n/t$ coefficients vanish. In particular there are at least $n/2$ nonzero coefficient residues, and at least $3n/4$ when the two sites are not opposite.

If the four locators jointly use $s$ degrees, their product uses at most $\binom{s+3}{4}$ different degrees, before or after cyclic reduction. For the joint support of $A,B$ of size $v$ one also has an upper bound $5\binom{v+3}{4}$, because the coefficient of $A^{4-j}B^j$ in the product has degree at most $j\le4$. These give the following minima.

| Physical support of the product | Joint locator degrees | Joint degrees of $A,B$ |
|---|---:|---:|
| Two sites | 336 | 224 |
| Two sites which are not opposite | 372 | 248 |
| One site | 400 | 267 |

These are necessary conditions for unrestricted half-rate witnesses. The finite checker tests the profile count, support and Fourier calculations, and replays the complete punctured example over $\mathbb F_{17}$. [Arithmetic and finite-field controls](../../../scripts/probes/probe_half_successor_sparse_heads.py)
