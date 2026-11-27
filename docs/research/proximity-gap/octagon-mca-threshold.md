# The exact half-rate MCA threshold on a smooth octagon

Let $D$ be any smooth eight-point evaluation coset in a finite field $F$ of order $q$, and take $k=4$. At two errors the maximum number of affine-line MCA-bad scalars is **seven in characteristics 3, 17 and 31, and six in every other admissible characteristic**. This gives different first failures on two smooth codes with the same length, dimension and 128-bit budget. The determinant classification is kernel-checked and the incidence argument is given below. [Lean certificate](../../../ArkLib/Research/ProximityGap/Frontier/OctagonCubicPencils.lean) · [Independent syndrome and received-word checks](../../../scripts/probes/probe_octagon_cubic_pencils.py)

Put $b=7$ in the three exceptional characteristics and $b=6$ otherwise. At tolerance $2^{-128}$ let $B=\lfloor q/2^{128}\rfloor$. The resulting MCA first failures are

| Budget | First failing error count |
|---|---:|
| $B=0$ | 0 |
| $B=1$ | 1 |
| $2\le B<b$ | 2 |
| $b\le B<56$ | 3 |
| $56\le B$ | Safe through radius one |

An entry $e>0$ gives safe real radii $[0,e/8)$ and last safe grid count $e-1$. The usual interleaving stability for affine-line MCA gives the same answer at every positive width. The companion list calculation gives a worst list of eight at three errors in characteristic three and seven in the other characteristics. [MCA stability](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCA.lean) · [Full octagon list threshold](syndrome-flat-list-profile.md)

## Counting actual bad scalars by secants

For a site $x$ write $v_x=(1,x,x^2,x^3)^{\mathsf T}$. The parity-check matrix has columns $v_x/\prod_{a\in D-\{x\}}(x-a)$. Indeed, every row annihilates the degree-below-four code by the leading-coefficient identity in Lagrange interpolation, and the matrix has rank four by Vandermonde. Thus its kernel is exactly the code and all syndromes are attainable. The span $W_E$ of the columns indexed by $E$ also equals the span of their unscaled $v_x$. A row agrees with a codeword off $E$ exactly when its syndrome belongs to $W_E$.

Take two received rows with syndromes $u,v$. On the witness with error sites $E$, the fold is bad just when $u+\gamma v\in W_E$ and the two syndromes do not both belong to $W_E$. For independent $u,v$, let $\ell=\mathbf P(\operatorname{span}(u,v))$. A supporting subspace that meets $\ell$ in a single point supplies one projective label. A subspace containing $\ell$ supplies none. Take the union of all supplied points, then omit the point at infinity to count affine labels. Any point of $\ell$ may be placed at infinity by choosing a basis for the same syndrome plane. With dependent $u,v$ there is at most one bad scalar, since only a zero fold can witness an error on a subspace that fails joint interpolation.

At two errors, the available spans are the vertices $[v_x]$ and their 28 secant lines. Any four vertices are independent. If $\ell$ itself is a secant, the only possible labels are its two vertices. If it passes through exactly one vertex $[v_a]$, the secants through that vertex contribute it once. A basis for the two linear forms annihilating $\ell$ restricts on $v_x$ to independent polynomials $A(x),B(x)$ of degree at most three, both divisible by $x-a$. After cancellation the seven remaining vertices map to $\mathbf P^1$ with fibers of size at most two. Each further secant hit pairs two vertices in the same fiber. Hence this case has at most $1+\lfloor7/2\rfloor=4$ labels.

Suppose $\ell$ misses every vertex. Project from it by the two annihilating forms, giving $x\mapsto[A(x):B(x)]$ on $D$. A secant meets $\ell$ exactly when its two vertices have equal image. Two different such secants give different labels. Secants joining disjoint pairs are skew, and secants sharing one vertex intersect only at that vertex, which lies off $\ell$. Every fiber has at most three sites, since each nonzero linear combination of $A,B$ is a polynomial of degree at most three. If the fiber sizes are $s_i$, the number of projective labels is exactly $\sum_i\binom{s_i}{2}$. With eight sites this is at most seven, and seven requires the partition $3+3+2$.

Six labels always occur. Choose any disjoint triples $S,T$, and for $A,B$ use their monic cubic locators $L_S,L_T$. The corresponding line misses the vertices. Each triple contributes three secants. The two remaining sites contribute a seventh precisely when their ratios coincide. Conversely every $3+3+2$ pencil has this form after changing the target coordinates, since a degree-at-most-three polynomial vanishing on three specified sites is a scalar multiple of their locator. An eight-point coset needs $q\ge9$, so even seven projective labels leave an unused point at infinity. All labels just counted can therefore occur simultaneously as affine folding scalars.

## The field-characteristic test

Rescale to $\mu_8$. Rotate the first leftover site to $1$ and write the other as $z^d$ for $1\le d\le7$ with $z$ a primitive eighth root. For a partition $S,T$ of the remaining exponents into triples, the seventh label occurs exactly when
\[
 \Delta=L_S(1)L_T(z^d)-L_S(z^d)L_T(1)=0.
\]
Here $L_S(X)=\prod_{j\in S}(X-z^j)$. Over $\mathbb Z[z]/(z^4+1)$ the 140 ordered partitions give the following ten distinct absolute norms.

| $d$ up to sign | Possible norms |
|---|---|
| 1 or 3 | 256, 1024, 18496, 246016 |
| 2 | 16384, 20736, 65536, 73984 |
| 4 | 4096, 16384, 331776 |

For $\Delta=a+bz+cz^2+dz^3$ its norm is $(a^2-c^2+2bd)^2+(2ac-b^2+d^2)^2$. The complete set of norms and their odd prime divisors are computed in Lean. In any field containing $z$ the norm is the product of the four determinants obtained at $z,-z,z^3,-z^3$. Each is a primitive eighth root indexing the same octagon. If the characteristic divides any norm, at least one factor vanishes and gives an actual partition. In the other direction every realizing partition has a vanishing norm. The odd primes dividing the table are exactly 3, 17 and 31. Characteristic two cannot supply a multiplicative octagon. [Norm identity and exceptional-characteristic equivalence](../../../ArkLib/Research/ProximityGap/Frontier/OctagonCubicPencils.lean)

## The other error counts

At zero errors only the zero syndrome works, giving at most one bad scalar, attained by $u=0$ and $v\ne0$. At one error a projective line contains at most two vertices by Vandermonde. The line through any pair attains two different labels after choice of chart.

At three errors each triple spans a projective plane. At most one bad scalar can be charged to each such plane. A smaller error set giving a bad scalar can be enlarged to a triple that still fails joint interpolation. To see this directly, on the agreeing sites interpolate the direction row on four anchors and keep one site witnessing failure of that interpolation. The fold still interpolates on these five retained sites. The same reduction applies to every larger error count. There are therefore at most $\binom83=56$ labels from three errors through radius one.

When $B\ge1$ the field has order at least $2^{128}$. All 56 labels occur in one affine chart. For the distinct triple planes choose normal forms $h_i$. First choose $v$ outside their union. Then choose $u$ outside the at most $\binom{56}{2}$ hyperplanes $h_i(u)h_j(v)-h_j(u)h_i(v)=0$. They are proper because the forms for distinct planes are independent. The elementary union bound permits both choices. The 56 scalars $-h_i(u)/h_i(v)$ are distinct, and $v$ fails membership in every plane. If $B=0$ the zero-error calculation already decides the first failure.

## Two fields with budget six

Over $\mathbb F_{17^{32}}$ the octagon has first MCA failure at **two errors**. Over the prime field of order $387\cdot2^{122}+1$ the octagon has first MCA failure at **three errors**. In both fields the first list failure at every positive width is **three errors**. Both have budget six and contain $\mu_8$. For the second modulus, 13 supplies the Proth certificate $13^{(q-1)/2}=-1\bmod q$. The independent verifier reconstructs actual received rows by inverting the syndrome map and directly checks Lagrange interpolation on every support of size at least six. Over $\mathbb F_{17}$ it also enumerates all 89,030 projective syndrome lines. The length-$2^{30}$ production intervals require separate estimates. [Verifier](../../../scripts/probes/probe_octagon_cubic_pencils.py)
