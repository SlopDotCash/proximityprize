# No saturated degree-seven quartet on the 32-site complex root subgroup

Let $W_0,\ldots,W_3$ be four pairs of polynomials of degree at most seven on $\mu_{32}$. Suppose the 32 sites consist of four singletons and 28 labelled double sites, the opposite edges of the quartet have equal populations, and every triangle has a nonzero face determinant vanishing on its fourteen double sites. Such a quartet cannot exist over the complex numbers. The proof does not assume affine symmetry of the layout, balanced edge populations, or distinct fresh directions. In particular it includes pairs of heads that agree on seven sites. The same exclusion holds at both named primes by the individual-ratio norm transfer below. The conclusion concerns this saturation pattern at length 32.

The final calculation proves the following slightly more general obstruction. No partition of the 32 exponents into six opposite edge colors and four holes can satisfy all three conditions below when the opposite sizes are $s_1,s_2,s_3\le7$ with sum fourteen.

1. The antipodal map $i\mapsto i+16$ changes the color on at least seven sites, with holes treated as one color.
2. Whenever an edge color occurs at least three times on one parity, the corresponding ternary signature is invariant under the antipodal map on the other parity.
3. The locator ratio for each color is constant on that color in the complex cyclotomic field.

These three conditions are necessary for a genuine saturated quartet. The first condition follows from the saturated face distance bound and the exclusion of a nonidentity rotation fixing all labelled double strata. If fewer than seven sites change, at least $28-6=22>3\cdot7$ double sites keep their pair label. The recovery argument then forces every label to be unchanged. The second condition is the dyadic parity theorem for a locator ratio at three roots of the same parity. The third follows by evaluating the signed relation among the four face determinants on each of its edge colors. [Distance and dyadic parity argument](quarter-dyadic-parity.md) · [Signed face equations](quarter-opposite-edge-characters.md#a-product-of-three-rational-functions)

## The six signatures

Order the colors as $A,a,B,b,C,c,H$, where lowercase letters denote opposite edges and $H$ denotes a singleton site. Regard each of the first six letters also as its monic root locator. After orienting the three opposite pairs, the four face locators are $ABC,Abc,aBc,abC$. Each ratio has signature equal to its vector of numerator exponents minus denominator exponents, with the hole column zero. The row for $A$ is $(0,0,+1,-1,-1,+1,0)$ and the row for $a$ is $(0,0,+1,-1,+1,-1,0)$. Cyclic permutation of the three pairs gives the other four rows. For example $B c/(b C)$ is constant on $A$ and $B C/(b c)$ is constant on $a$. Each ratio is defined at every site on which it is tested.

We may sort $s_1\le s_2\le s_3$ by relabelling the vertices and order the two parity population vectors lexicographically by an index translation. For a parity containing a heavy color (at least three occurrences), its corresponding signature partitions the opposite parity into three classes. Intersect all the partitions coming from that parity's heavy colors. Two sites exchanged by the antipodal map must lie in the same class. Every resulting class therefore has even total size $T$. If its largest color has $m$ sites, at most $\min(T,2(T-m))$ sites can change color. Applying these tests in both parities and enforcing the distance bound leaves **195** parity population vectors.

## Valuations on the residue tree

Let $\zeta$ be a primitive complex thirty-second root and normalize the valuation at $1-\zeta$ to have value 1 there. For $i\ne j$,
\[
 v(\zeta^i-\zeta^j)=2^{v_2(i-j)}.
\]
Indeed $1-\zeta^k$ has the same valuation as $1-\zeta^{2^e}$ for $k=2^e u$ with $u$ odd: the quotient is a sum of an odd number of roots, hence a unit at this place. In each doubling before order two, $1-\zeta^{2^e}$ and $1+\zeta^{2^e}$ have equal valuation by a Galois conjugation. Their product gives the next doubling.

For a color $h$ with signature $r_h$ let $C(j)$ be the color at position $j$. The sum
\[
 P_h(i)=\sum_{j\ne i}2^{v_2(i-j)}r_h(C(j))
\]
is the valuation of its locator ratio at a site of color $h$. Thus $P_h$ must be constant on that color. This imposes six separate constancies. The computation uses no equation relating the six constant values to each other.

A residue block with $m$ sites splits by the next index bit into two children. The weight between sites from different children equals $32/m$. A site in the left child receives the same contribution from the right child as every other left site of its color: multiply $32/m$ by the signature row dotted with the right population vector. The same rule holds with left and right exchanged. Contributions from outside the whole block are constant across its sites for each fixed signature. One can therefore reject a block immediately when a color has incompatible potential values, without losing any extension. A two-site leaf block is an antipodal pair; its cross weight is sixteen and its two colors obey the heavy-signature conditions.

The dynamic program records the six potential values on nonempty colors and the number of changed sites. It enumerates every split of a population vector and joins child states by the equality just proved. Reversing children is included when their population vectors differ; for equal populations the Cartesian product already contains both orders. At the top it joins even and odd blocks with weight one. Exactly **35** of the 195 population profiles survive, representing **6,490,722,304** ordered layouts in the stated normalization.

## Exact final specialization

Inside the even half write $i=2j$. Every affine bijection $j\mapsto uj+b$ of $\mathbb Z/16$ extends to $i\mapsto ui+2b$ on $\mathbb Z/32$. Translating indices scales each locator by the appropriate root of unity, and multiplying by an odd unit acts on the complex roots by Galois conjugation. These operations preserve the same-color ratio identities, valuations, and antipodal comparisons. We can therefore choose one even half in each such orbit and keep every eligible odd half. This leaves **73,967,616** representative pairs.

Set $p=65537$ and specialize $\zeta$ to $3^{2048}\bmod p$. Its 32 powers are distinct. Every same-color ratio comparison can be cross-multiplied in $\mathbb Z[\zeta]$ and all its denominators specialize to nonzero differences. Consequently every complex solution passes the comparisons in this one finite field. The probe constructs the exact base-3 discrete logarithm table and, for every site and parity subset, sums the logs of its root differences modulo $65536$. The signed lookup for a color is the sum on its positive subset minus the sum on its negative subset. Checking the first two sites of one repeated even color leaves **314,846** representatives. Checking constancy on every site of all six colors leaves **zero**.

Run `python3 scripts/probes/probe_quarter_32_parity_tree.py`. It assembles the eligible layouts in temporary files, compiles the finite-field checker, and verifies the counts. This is a reproducible finite computation. The 73,967,616-case screen has not been replayed in the Lean kernel. [Parity and valuation enumeration](../../../scripts/probes/probe_quarter_32_parity_tree.py) · [Finite-field ratio checks](../../../scripts/probes/probe_quarter_32_parity_faces.cpp)

## Application to the named prime fields

For a saturated 32-site quartet in either named field, the antipodal distance bound applies within that field. It suffices to transfer each same-color ratio comparison separately to $\mathbb Q(\zeta_{32})$. If a color has at least two sites, the positive and negative sides of its ratio each have size $14-s_i\le12$. Colors with zero or one site require no ratio comparison. Once these identities transfer, the complex dyadic parity theorem applies and the finite calculation above gives the same contradiction. The size-32 exclusion uses the odd-norm bound for these particular ratios. A production-length quartet need not descend from a 32-site saturated template. [Cyclotomic norm transfer](mu32-odd-ratio-norm.md) · [Independent unit-kernel sieve](quarter-mu32-unit-sieve.md)
