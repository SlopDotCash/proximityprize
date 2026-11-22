# Every locator-ratio comparison lifts at order 128 in both named fields

Let $z$ be a primitive 128th root in either named prime field. For disjoint subsets $P,Q$ of the exponents and sites $x,y$ outside them, set
\[
 L_S(T)=\prod_{s\in S}(T-z^s),\qquad
 R=\frac{L_P(z^x)L_Q(z^y)}{L_Q(z^x)L_P(z^y)}.
\]
Fix the corresponding complex primitive root with the same exponent convention. Reduction takes every complex equality $R=1$ to the finite field. **The converse holds for every choice of the two supports and two centers.** This follows from the complete logarithms of the 32 units $u_r=1-z^r$ with odd $1\le r<64$.

## The displacement matrix

Translating every exponent makes the first center zero. If necessary, exchange the centers and translate again to obtain $1\le h\le64$. Scaling all points by the same root preserves $R$ even when $|P|\ne |Q|$. The two centers lie outside both supports. Write $w_j=1_P(j)-1_Q(j)$ on the 126 remaining exponents. Define the integer matrix
\[
 \Phi_r(j)=\#\{(a,\epsilon)\mid 0\le a<7,\ \epsilon=\pm1,\ j\equiv\epsilon 2^ar\bmod128\},\qquad
 A_{rj}=\Phi_r(j)-\Phi_r(j-h).
\]
For nonzero $t=2^a b\bmod128$, with $b$ odd, factor $1-z^t$ into $1-z^{b+128k/2^a}$ for $0\le k<2^a$. Replacing an odd exponent by its negative only introduces a power of $z$. Hence $R=z^v\prod_r u_r^{e_r}$, where $e=Aw$, and the same integer phase $v\bmod128$ works in both fields. The two signs in $\Phi_r(64)$ both contribute. At $h=64$ every column sums to zero because $j$ and $j-64$ have the same 2-adic valuation. Drop the last coordinate and subtract its logarithm from every remaining logarithm.

Let $S=AA^{\mathsf T}$ in the resulting 32 or 31 coordinates. The verifier checks $S$ is positive definite and computes its rational inverse. For $y=S^{-1}e$, expansion of $\|w-A^{\mathsf T}y\|^2\ge0$ gives
\[
 e^{\mathsf T}S^{-1}e\le\|w\|^2\le126.
\]
The first inequality is formalized for arbitrary finite rational matrices. [Lean energy inequality](../../../ArkLib/Research/ProximityGap/Frontier/DyadicUnitEllipsoid.lean)

## The finite-field check

For a primitive generator $g$ of the field, let $l_r=\log_g u_r$ and $M=(p-1)/128$. If $R=1$, then $l\cdot e=0\bmod M$. The certificate verifies recursive primality witnesses, the multiplicative order of $g$, all 32 full-field logarithms by exponentiation, and the order of $z$. The primitive generator is 3 at the first named prime and 37 at the second.

A row Hermite basis $H$ for the integer column image of $A$ reduces the enumeration. The verifier checks directly that every source column is an integer combination of the basis rows. In this basis a sequence of Bézout operations produces generators for the single congruence $l\cdot e=0\bmod M$. Each generator satisfies the congruence and the absolute determinant equals its exact index. The image-basis indices for displacements $1,2,4,8,16,32,64$ are respectively $1,2,4,16,256,65536,2^{26}$, with the last index taken after dropping a coordinate.

The verifier reduces the Gram matrix in the metric $S^{-1}$ by a checked unimodular change of basis. Exact rational Gram–Schmidt lengths and integer square roots enumerate the closed ellipsoid, including its boundary. The enumeration found only the origin in all 64 displacement ellipsoids at each named prime. Reversing the initial congruence basis and rerunning gave the same 128 singleton results. Thus $e=0$ and $R=z^v$. Since both roots have order 128, the finite-field equality then forces $v=0\bmod128$, so $R=1$ over the complex numbers. A different choice of primitive root in the finite field permutes the exponent labels by an odd multiplier. The corresponding complex permutation is a Galois automorphism.

The [full logarithms](../../../scripts/probes/mu128_unit_logs.json) were obtained by index calculus and checked by modular exponentiation. Each logarithm can be verified independently of the program that found it. The [exact verifier](../../../scripts/probes/probe_mu128_unit_ellipsoid.py) requires Python 3 and `python-flint`. Run `python3 scripts/probes/probe_mu128_unit_ellipsoid.py`, optionally with `--reverse-basis`. The Lean energy inequality, together with the order-256 arithmetic comparison below, passed the locked build and independent verified kernel replay with 5,843 transitive declarations. The lattice enumeration is executable integer arithmetic.

## Single-anchor locator values and roots of unity

Fix a site $z^a$ and any two subsets $P,Q$ of $\mu_{128}$ avoiding it. For each named prime and integer $c$,
\[
 L_P(z^a)=z^c L_Q(z^a)\quad\Longleftrightarrow\quad
 L_P(\zeta^a)=\zeta^c L_Q(\zeta^a)
\]
with the same exponent labels at the complex primitive root $\zeta$. Here the two evaluations of $L_P$ and $L_Q$ use the corresponding roots in their respective fields. Neither the cardinalities nor the root products of $P,Q$ need coincide.

Translate the exponents by $-a$ and form $w_j=1_{P/z^a}(z^j)-1_{Q/z^a}(z^j)$ for $1\le j<128$. This time $A_{rj}=\Phi_r(j)$, with no second-site term. The ratio is $z^v\prod_r(1-z^r)^{(Aw)_r}$, including the translation factor $z^{a(|P|-|Q|)}$ in $z^v$. The same factorization holds over the complex numbers. The projection inequality gives $(Aw)^\mathsf{T}(AA^\mathsf{T})^{-1}(Aw)\le\sum_jw_j^2\le127$. For two nine-element supports the source bound improves to 18. The 32 columns at positive odd exponents below 64 already form the identity matrix, so the column image is all of $\mathbb Z^{32}$.

A field ratio in $\mu_{128}$ imposes $l\cdot Aw\equiv0\pmod{(p-1)/128}$. At squared radius **127**, the closed ellipsoid contains exactly the zero vector of this congruence lattice at each prime, with both basis orders. Thus a ratio in $\mu_{128}$ requires $Aw=0$. Conversely $Aw=0$ makes the ratio exactly $z^v$, and the two primitive roots have the same order, so a specified exponent $c$ works in both fields. Complex equalities also specialize directly after clearing denominators.

For the rate-$1/16$ witness the relative supports avoid the entire order-16 subgroup. The column $\Phi_r(j)$ counts the visits to $\{j,-j\}$ along the successive doublings of leaf $r$. Consequently $A1_T$ is precisely the leaf vector, in the order of the primitive odd representatives. For two equal-size supports with equal leaf vectors, the complex arguments of their locators at one differ by $\pi(\sum_{j\in T}j-\sum_{j\in T'}j)/128$, using representatives $1\le j<128$. Their absolute values agree by the leaf norm formula. Hence equality at the anchor is equivalent to equality of the leaf vectors **and** of the exponent sums modulo 256. At fixed root product the latter datum is a single sign bit. The criterion holds for all such supports, including vectors omitted by a ranking cutoff. [Signed modes and actual field labels](sixteenth-locator-union.md#actual-field-symbols-at-the-fifteen-anchors)

Run the same exact verifier with `--single-anchor` and then with `--single-anchor --reverse-basis`. Both runs also check the primitive-vector entries against the reciprocal-pair tree for every ordinary exponent. Independently evaluating 3,276 nine-element sets at each prime gives 3,270 distinct signed labels and the same number of distinct values, including both a repeated label and sign splits. Raising the values to the 128th power checks the equivalence up to a root of unity on this control. [Exact verifier](../../../scripts/probes/probe_mu128_unit_ellipsoid.py)

## The two coding consequences

At quarter rate a saturated rank-two group of four affine heads at 64 errors would give six constant locator-ratio rows, each on its own double stratum. All the required pairwise comparisons now lift. The complex three-center parity lemma and the six label signatures then leave at most ten changed double labels under negation. The finite-field label-recovery and odd-degree rotation obstruction requires at least $d=31$ changed labels. Such a group cannot occur. [Parity, label recovery and rotation](quarter-dyadic-parity.md)

At half rate the maximum number of codewords in a Hamming ball of radius **33** is exactly **three**. The overlap classification for four scalar codewords gives either a three-split pencil with root sets of size 31 or a four-cycle. All the constant locator ratios in these cases lift. The complex pencil parity bound would require $3(31-2)\le64$, while the cycle contradicts its parity counts. The geometric-sum center with $M=4$ and $h=32$ attains three. At positive interleaving width any four distinct vector polynomials admit a scalar projection keeping the four distinct. Select a nonzero coefficient vector from each of the six pair differences and choose a linear functional outside the union of their six annihilating hyperplanes, possible since $p>6$. Projection preserves each agreement with the received word, while padding the scalar example gives the lower bound. [Overlap classification](dyadic-radius-successor-list-three.md) · [Geometric-sum center](PROGRESS.md#2026-11-21--exact-list-of-the-geometric-sum-center)

## Limit of the single-comparison ellipsoid argument

At order 256 and displacement two, let $A$ use all 64 primitive coordinates and all 254 sites outside the centers. The integer image contains a sublattice of index two. The verifier checks an integral combination matrix realizing the Hermite generators. It also computes
\[
 \det(AA^{\mathsf T})=614560623940147206055138107999571273706286146912256.
\]
Intersect that sublattice with the single logarithm congruence modulo $(p-1)/256$. The resulting determinant is at most $2(p-1)/256$. The 64-dimensional ellipsoid of squared radius 74 has volume $\pi^{32}74^{32}\sqrt{\det(AA^{\mathsf T})}/32!$. Even using $\pi>3$, its volume exceeds $2^{64}$ times the determinant at both primes. Minkowski's convex body theorem places a nonzero lattice point inside. Thus the relaxation alone already admits a nonzero relation at squared radius 74, substantially below the full ternary energy bound 254. The estimates concern an integer exponent vector in the relaxed ellipsoid. Actual locator supports additionally require a ternary source and the correct phase. [Lean squared volume comparison](../../../ArkLib/Research/ProximityGap/Frontier/DyadicUnitEllipsoid.lean) · [Exact determinant and image check](../../../scripts/probes/probe_mu128_unit_ellipsoid.py)
