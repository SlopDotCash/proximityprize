# Septic pencils on the 128-site subgroup

In either named prime field, suppose two degree-seven polynomials have disjoint sets of seven roots on \(\mu_{128}\). Their ratio takes any given finite nonzero value at **at most five** other subgroup sites. The same bound holds over the complex numbers. Consequently four distinct degree-at-most-seven words on these 128 sites have at most **39** useful pair coincidences. The worst list at 86 errors is exactly **three**, at any positive interleaving width. The first error count admitting four words is either **87 or 88**.

At the second prime's length-\(2^{30}\), rate-\(1/16\) MCA pivot this rules out every four-word common-multiplier construction that factors through a power quotient of order at most 128. The unrestricted worst list at that pivot is still either three or four. [Prior quotient reduction and three-word construction](cubic-list-padding.md)

## Six test sites and the cyclotomic equations

Identify exponents with \(\mathbb Z/128\). Write \(\zeta\) for the complex primitive root and \(L_A\) for the monic locator of a set \(A\). All ratios can be taken monic by rescaling the value of the fiber. If \(L_A/L_B\) is constant on six sites in either field, then every two-site comparison lifts to the complex numbers with the same exponents. Conversely any complex equality specializes at either named prime, as these sites avoid the zeros of both factors. This also permits odd Galois multipliers in the enumeration, even at prime fields with no nontrivial field automorphisms. [Order-128 transfer at both named primes](mu128-unit-ellipsoid-transfer.md)

At least three test exponents have one parity. Rotate so three are even. The complex three-center parity lemma then forces both \(A\) and \(B\) to be antipodally symmetric on the odd exponents. If three test exponents were also odd, the supports would be antipodally symmetric on both parities, contradicting their odd size seven. The rational function \(L_A/L_B\) is fixed by the automorphism \(\zeta\mapsto-\zeta\), since its even roots are fixed and its odd roots are paired. Its value at any even test point is fixed as well. Each odd test point therefore brings its antipode into the same fiber. We may choose six even test points or four even points and one odd antipodal pair. This reduction also covers five even test points with a single odd test point. [Three-center parity lemma](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

Write even exponents as \(2i\) with \(i\bmod64\). In the six-even case translate one point to zero and enumerate the six-subsets containing zero up to \(i\mapsto u(i-v)\), for every odd \(u\bmod64\) and every member \(v\) of the set. This gives **38,494** orbits. In the other case normalize the odd pair to \(\{1,65\}\). Its stabilizer acts on the four even indices by \(i\mapsto ui+(1-u)/2\) and \(i\mapsto ui+(65-u)/2\) for odd \(u\bmod128\). Enumerating all four-subsets gives **9,952** orbits.

For odd \(1\le r<64\), put
\[
 \Phi_r(d)=\#\{(j,\epsilon):0\le j<7,\ \epsilon=\pm1,\
                 d=\epsilon 2^j r\bmod128\}.
\]
Set \(w_a=1_A(a)-1_B(a)\). For any two sites \(x,t\) of the fiber,
\[
 \sum_a w_a \bigl(\Phi_r(a-x)-\Phi_r(a-t)\bigr)=0
       \qquad(1\le r<64,\quad r\ \mathrm{odd}).
\]
These are the primitive-unit exponents of the locator cross-ratio. The order-128 transfer certificate forces the exponent vector itself to vanish in a field equality. A complex equality gives the same conclusion by specialization. [Displacement matrix and certificate](mu128-unit-ellipsoid-transfer.md#the-displacement-matrix)

## Exact finite search

Reduce these equations modulo three. The signed symbols \(0,1,-1\) remain distinct. There are 96 unknowns, one for each even exponent, with weight one, and one for each of the 32 odd antipodal pairs, with weight two. Force every tested coordinate to zero and impose \(\sum_a w_a=0\bmod3\). Choose a base test site and use all 32 equations for each of the five other sites. Enumerate the resulting ternary kernel by Gaussian elimination. A candidate must have positive weight seven and negative weight seven as ordinary integers. The search assigns all three possible coefficients to each kernel basis vector. It prunes only when the fixed positive or negative weight already exceeds seven. A coordinate is fixed if every unassigned basis vector vanishes there.

Across all **48,446** orbits there are six directed candidate pairs. The table gives the three pairs up to exchange. All exponents below are on the full 128-site grid. The last column is the maximum multiplicity of any nonzero finite ratio on the entire grid, independently evaluated at each prime.

| Test exponents | First support | Second support | Maximum |
| --- | --- | --- | ---: |
| 0,8,16,40,48,64 | 6,20,38,70,84,96,102 | 4,12,32,36,68,76,100 | 4 |
| 0,2,28,32,60,66 | 34,44,58,92,98,122,124 | 8,12,40,52,56,88,116 | 4 |
| 0,4,8,56,68,80 | 24,28,40,52,64,92,116 | 20,44,72,84,96,108,112 | 1 |

Thus none of the candidates has all six prescribed test values equal. Run \(\texttt{python3 scripts/probes/probe_mu128_septic_kernel.py}\), optionally with \(\texttt{--reverse-pivots}\) to reverse Gaussian pivot order. The verifier builds the C++17 enumerator in a temporary directory, checks both field specializations and verifies the combinatorial and radius calculations. [Enumerator](../../../scripts/probes/probe_mu128_septic_kernel.cpp) · [Independent field checks](../../../scripts/probes/probe_mu128_septic_kernel.py)

## Four-word consequence

For four scalar polynomials let \(r_{ij}\) count sites where words \(i,j\) agree. At each site \(x\), let \(r(x)\) count equal word pairs and let \(c(x)\) be the largest number of equal words minus one. The useful coincidence count is \(C=\sum_x c(x)\). Each \(r_{ij}\le7\). Put \(D=\sum_{i<j}(7-r_{ij})\) and \(W=\sum_x(r(x)-c(x))\), so \(42-C=D+W\). A triple match costs one unit of \(W\), two disjoint matching pairs cost one unit, and a quadruple match costs three.

Suppose \(C\ge40\). Then \(D+W\le2\), so a quadruple site is impossible and at most \(W\) triples of word indices contain an all-equal site. A triple of word indices is eligible if two of its pair differences have seven roots and the third has at least six. When \(D=0\), all four triples are eligible. With \(D=1\), all four are again eligible. When \(D=2\), a single deficient edge leaves a full triangle avoiding it. Two edges deficient by one leave a triangle containing at most one of them. In every case more than \(W\) triples are eligible. Pick one without an all-equal site. Its three root sets are pairwise disjoint, since a root common to two differences in this triple makes all three values equal. Take the common endpoint of the two fully split edges as the first word. The two differences with that word are scalar multiples of the locators of disjoint seven-element sets. Their ratio is one at the six or more roots of the third difference, contradicting the census. Thus \(C\le39\).

At radius 86, four words would need \(4\cdot42>128+39\) agreements. Three different constant words can each be assigned 42 private sites. Four words at radius 88 come from the known four cubics on the order-32 subgroup, evaluating them at \(X^2\) on the order-128 grid. The image of the squaring map is (mu_{64}), which contains (mu_{32}). The sixteen prescribed double-match sites each have two preimages, securing respectively 18, 14, 16 and 16 hits. Assign respectively 22, 26, 24 and 24 of the 96 other sites to obtain 40 hits apiece. At positive width project through a linear functional keeping all six pair differences nonzero. Such a functional exists since the field has more than six elements. Projection preserves every received-word agreement. Repeating a scalar example supplies the matching construction at any width. [Integral cubic witnesses](mu32-list-threshold-large-characteristic.md#dimension-four-at-the-same-length)

For the length-\(2^{30}\) reduction write \(s=n/128\), \(d=n/16-1\), and consider words \(A(X)+J(X)F_i(X^s)\) with \(D=\max_i\deg F_i\) after subtracting a common word, and \(\deg J+sD\le d\). Total agreements are at most \(n+3d+s(C-3D)\). If \(D=7\), the new bound \(C\le39\) is one below the necessary 40. If \(D\le6\), the pair bound \(C\le6D\) already falls short. Thus a witness through this class must have a quotient of at least 256 sites. Four arbitrary words on the length-\(2^{30}\) grid remain a separate question. [Pivot arithmetic and lower bounds](cubic-list-padding.md#what-a-four-word-power-map-construction-would-require-at-the-pivot)
