# No saturated degree-seven four-head seed on the two named 32-site subgroups

On $H=\mu_{32}$ over either named prime, and in characteristic zero, no noncollinear saturated quartet of vector heads of degree at most seven exists. This includes the patterns required for four heads to exceed $64$ fresh labels at the quarter-rate seam. The statement concerns four heads and does not give a complete MCA threshold at length 32.

## A uniform lift of every vanisher-ratio comparison

Fix a primitive root $\zeta$ of order 32. For $r=1,3,\ldots,15$, write $u_r=1-\zeta^r$. Every difference of two distinct subgroup points is a root of unity of order dividing 32 times a monomial in the $u_r$. In fact if $d=2^a d'$ with $d'$ odd, factor $1-\zeta^d$ as the product of the $2^a$ factors $1-\zeta^{d'+32j/2^a}$. Replacing a negative odd representative by its positive opposite changes the product only by a root of unity. Denote the resulting vector of eight nonnegative exponents by $\Phi(d)$.

In any one coordinate the sum over the 31 nonzero differences of $\Phi(d)$ is 10. Each of the four valuations $a=0,1,2,3$ gives two occurrences, and the single difference 16 gives two more. For disjoint subsets $P,Q$ and test sites $x,y$ outside them, the ratio
\[
 \frac{L_P(x)L_Q(y)}{L_Q(x)L_P(y)}
\]
therefore has all eight unit exponents between $-20$ and $20$. Indeed it sums the differences of the two translated $\Phi$ rows with weights $1_P-1_Q$.

For each named prime, exact finite-field arithmetic checks that
\[
 \prod_{r=1,3,\ldots,15} u_r^{32e_r}=1,\quad |e_r|\le20
 \quad\Longrightarrow\quad e_r=0\ \hbox{for every }r.
\]
The checker enumerates the $41^4=2825761$ products on each half of the factors and compares exact residues. The left products are distinct. The unique match with the right half is the common zero-exponent product. The bound on the signed exponents is unchanged if the right exponents are negated. Once the unit vector vanishes, the original expression is a power of $\zeta$ in every characteristic. Its phase is one exactly when its exponent is divisible by 32. Thus every comparison of two vanisher-ratio values lifts from either named prime to characteristic zero. There is no degree or size restriction on the disjoint subsets. The chosen primitive root is immaterial, since any alternative permutes the eight representatives up to sign and torsion. [Exact bounded-unit check](../../../scripts/probes/probe_mu32_unit_injectivity.py)

## Exhausting the characteristic-zero configurations

Write $(A,A'),(B,B'),(C,C')$ for the opposite edge pairs, identifying each set with its monic locator. A saturated quartet has equal sizes for opposite sets, sizes at most seven, and the three sizes sum to fourteen. Four sites are holes. Its signed face relation makes $BC'/(B'C)$ constant on $A$, and $BC/(B'C')$ constant on $A'$, with cyclic analogues for the other four sets. The preceding lift applies separately to all six tests. [Signed face relation](quarter-opposite-edge-characters.md)

In characteristic zero the eight $u_r$ are multiplicatively independent modulo roots of unity. Thus for each fixed largest side $A$, and $P=B\cup C'$, $Q=B'\cup C$, the ternary vector $w=1_P-1_Q$ belongs to the integer kernel of the rows
\[
 \Phi(j-t)-\Phi(j-t_0),\qquad t\in A\setminus\{t_0\},\quad j\notin A,
\]
read coordinate by coordinate. Translations and all odd exponent multipliers preserve these characteristic-zero requirements. Normalize $A$ by these actions. Its size is five, six or seven. [Cyclotomic independence and parity argument](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

For each representative, the checker row reduces the eight-coordinate differences modulo 101 and enumerates the three possible values at every free column. It retains exactly the ternary pivot solutions with $|P|=|Q|=14-|A|$. It orders the two sets lexicographically, which only interchanges $B,B'$ and $C,C'$ simultaneously. It then checks the literal first ratio in the auxiliary field of order 65537. Every characteristic-zero identity specializes since no differences between distinct subgroup points vanish. To enumerate the opposite row choose $B\subseteq P$ and $B'\subseteq Q$ of each common possible size, including zero. On the unused sites evaluate $(B/B')^2 Q/P$. Every $|A|$-element subset of any constant fiber is tried for $A'$. Finally require the six literal ratio conditions, including any vacuous empty loci.

| Largest size | Affine exponent orbits of the chosen side | Maximum free columns | Unordered first pairs | Oriented layouts after the opposite test | After all six tests |
|---:|---:|---:|---:|---:|---:|
| 5 | 454 | 6 | 0 | 0 | 0 |
| 6 | 1943 | 6 | 57 | 1886 | 2 |
| 7 | 6903 | 5 | 0 | 0 | 0 |

In both survivors every old double stratum is closed under $x\mapsto -x$. The complete search was repeated with pivot reductions modulo 103. The two reported layouts differ only in the names and orientations of two opposite pairs. Their possible lift as signed face relations is unnecessary for the exclusion. [Complete ternary and orientation search](../../../scripts/probes/probe_quarter_mu32_unit_sieve.py)

For any rank-two saturated quartet the two rows of translated head differences are independent at zero and, after degree-seven homogenization, at infinity. Labelwise invariance makes their pullbacks under the half-turn scalar splines for exactly the same equalities. The degree-seven spline space is exactly the span of the two original rows, so the half-turn acts on their span by a constant matrix. At infinity the leading coefficients force this matrix to be $-I$. At zero they force it to be $I$, a contradiction in the characteristics considered. Thus both residual layouts are impossible for heads. [Scalar row rigidity](quarter-saturated-birational.md#why-a-rational-cover-repeats-fresh-labels) · [Rotation theorem](../../../ArkLib/Research/ProximityGap/Frontier/SaturatedTripleRotation.lean)

## The two-center reflection

There is also a useful refinement independent of the finite search. In the characteristic-zero parity proof let $v$ be the signed antipodal difference on the exponent parity opposite two distinct test centers $x,y$, extended by zero to the full cyclic group. Comparison of the unit exponents gives equality of the symmetric translates $v(x+i)+v(x-i)=v(y+i)+v(y-i)$ for all $i$. Put $D(j)=v(j)-v(x+y-j)$. Substituting $i=j-x$ shows $D(j)=D(j+y-x)$. In a cyclic group of order a power of two the subgroup generated by the nonzero displacement contains the half-turn. The function $D$ is antiperiodic under that half-turn, so $D=0$. Thus two test sites force reflection of $v$ about their midpoint on the opposite parity. Lean checks the reflection implication and verifies every nonzero displacement reaches the half-turn in the order-32 case. [Lean reflection proof](../../../ArkLib/Research/ProximityGap/Frontier/DyadicTwoCenterReflection.lean)
