# Five consecutive evaluations determine a dyadic locator in characteristic zero

Let $H=\mu_n$ with $n=2^k\ge8$ in characteristic zero. Write $L_A(X)=\prod_{a\in A}(X-a)$ and index the roots by powers of a primitive root. If disjoint $P,Q\subset H$ have $L_P/L_Q$ equal to the same nonzero value at five consecutive exponent sites outside $P\cup Q$, then $P=Q=\varnothing$. Consequently five such evaluations of an unknown monic locator, known up to a common scalar, determine its entire root subset away from those sites. The same holds along a progression with odd step, by changing the primitive root. No degree bound is needed.

More generally, the sites can meet any three even residue classes modulo eight and two odd classes distinct modulo four, or the parity-swapped pattern. For the second case rotate the exponents by one. Scaling the argument of a locator ratio by a root of unity multiplies it by a constant when the two degrees differ.

## Why a fifth site suffices

Let $\zeta$ generate $H$. Three distinct even centres with the same ratio imply that the two sets of odd exponents in $P,Q$ are separately closed under addition of $n/2$. This is the dyadic three-centre theorem for signed locator indicators. It uses the independence modulo torsion of $1-\zeta^r$ for odd $r$ modulo sign. [Three-centre proof and independence](quarter-dyadic-parity.md#three-equal-ratios-in-one-parity-class)

Both monic locators now have coefficients in $K=\mathbb Q(\zeta^2)$. Their even roots lie in $K$, and each pair of opposite odd roots contributes $X^2-\zeta^{2r}$. Their common ratio value lies in $K$ by evaluation at an even centre. The automorphism of $\mathbb Q(\zeta)/K$ sending $\zeta$ to $-\zeta$ therefore takes each odd centre to a further centre with that same value. Two odd centres distinct modulo four have disjoint antipodal pairs, since $4\mid n/2$. This gives four distinct odd centres. Applying the three-centre theorem to three of them makes the even parts of both supports antipode-closed too. [Lean conjugation of evaluations](../../../ArkLib/Research/ProximityGap/Frontier/LocatorConjugateCentres.lean)

The map $x\mapsto x^2$ now sends each support to a disjoint support on $\mu_{n/2}$ and $L_P(X)=L_{P^2}(X^2)$, with the same formula for $Q$. Indeed each pair $\{a,-a\}$ contributes $X^2-a^2$. The marked images remain disjoint from the supports and have constant ratio. As long as $n/2\ge8$, reduction of the exponents modulo $n/2$ preserves the prescribed residue classes modulo eight. At the step from eight to four the marked images exhaust $\mu_4$: the three even residues cover both even residues modulo four, and the two odd residues are distinct there. The two supports must be empty, and hence were empty on $H$.

Four consecutive sites do admit a nonconstant ratio. On $\mu_{32}$ take the exponents
$$
 P=\{5,11,12,14,21,23,24,30\},\qquad
 Q=\{6,7,8,13,22,27,28,29\}.
$$
The cross products $L_P(\zeta^i)L_Q(1)$ and $L_Q(\zeta^i)L_P(1)$ agree for $i=1,2,3$ and differ for $i=4$. The verifier performs all multiplications in $\mathbb Z[Z]/(Z^{16}+1)$. Pullback along $X^{n/32}$ proves sharpness for every dyadic $n\ge32$, with two disjoint supports of size $n/4$. The order-32 and order-64 transfer theorems give the same sharp five-site result on both named prime fields at those lengths. [Exact four-site check](../../../scripts/probes/probe_five_dyadic_centres.py) · [Finite-field transfer](mu64-unit-lattice-transfer.md)

## Collisions at millions of prescribed finite-field sites

Fix the production length $n=2^{30}$, and a test set $T$ of the indicated size satisfying the five-site residue condition. At either named prime, there exist two disjoint, nonempty, equal-size subsets off $T$ whose monic ratio is constant on $T$ but fails that test over the complex numbers. The joint row gives the same exponent subsets for both primes, for any primitive root chosen in each field. At each prime the constant may differ.

| Fields tested simultaneously | Prescribed sites $t$ | Upper bound on each reduced degree |
|---|---:|---:|
| First | 5,473,612 | 267,066,368 |
| Second | 5,439,375 | 267,075,584 |
| Both | 2,735,180 | 267,751,424 |

Write $q=p-1$ for one prime and $q=(p_1-1)(p_2-1)$ for both. Partition as much of the complement as possible into $b=\lfloor(n-t)/4096\rfloor$ blocks of size 4096. Choose exactly 1024 sites from each. There are $\binom{4096}{1024}^b$ different monic locators of degree $1024b$. Their evaluation vectors on $T$, normalized by a fixed base coordinate, have at most $q^{t-1}$ values. The displayed counts satisfy $q^{t-1}<\binom{4096}{1024}^b$. Hence two distinct supports have the same normalized vector. Cancel their common roots. The two disjoint remaining supports are nonempty and have equal degree at most $1024b$. The five-site theorem distinguishes these locators in characteristic zero. The integer verifier uses $2^{3316}<\binom{4096}{1024}$ and small power comparisons for $q$. At order 1024 a nonlifting collision of degree at most 255 already exists on any five consecutive sites of either named prime, since $\binom{1019}{255}>(p_2-1)^4$. [Exact counts](../../../scripts/probes/probe_five_dyadic_centres.py)

### Any prescribed sites of one parity

There is a different guarantee when all the marked sites have one parity and can occupy arbitrary residue classes. Rotate to make them even. Give each of the $m=n/4$ odd antipodal pairs its own unmarked even filler, possible when $t\le n/4$. Choose exactly one of the three sites in each block. If $3^m>q^{t-1}$, two of these locators have the same normalized evaluation vector. Cancel their common choices. At a differing block, the signed indicator $1_P-1_Q$ differs on the odd antipodal pair, whether the two choices used both odd sites or one odd site and its filler. Thus the complex ratio has **at most two occurrences of any one value on the marked sites** by the three-centre theorem. A single residue collects at least $\lceil t/2\rceil$ distinct complex values. Off the supports, evaluating and reducing the signed locator ratio commutes with specialization of the primitive root. The degree bound $m$ can be reduced to $m-1$ by reserving one whole block whenever $3^{m-1}>q^{t-1}$.

| Fields | Arbitrary same-parity sites $t$ | Distinct complex values, at least |
|---|---:|---:|
| First | 2,692,786 | 1,346,393 |
| Second | 2,675,850 | 1,337,925 |
| Both | 1,342,146 | 671,073 |

For each row, $q^s<3^r$ and $(t-1)r\le ms$ hold for $(r,s)=(21333,214),(28089,280),(41601,208)$ respectively. In fact the inequality still holds with $m-1$ in all three rows. At order 1024, $3^{256}>(p_2-1)^2$ gives such a collision for every prescribed same-parity triple at each named prime. Lean verifies the ternary collision for an arbitrary finite abelian group, including the signed imbalance after cancellation, and the one-field and joint production integer comparisons. The assembly with the complex three-centre theorem and the mixed-parity counting argument are written proofs. [Lean collision and arithmetic](../../../ArkLib/Research/ProximityGap/Frontier/TernaryLocatorCollision.lean)

The production split-pencil tests also require a prescribed exact degree and complete fibers or several related locator ratios. These examples resolve the uniform lifting question for the protected-site counts above. They leave those additional prize conditions open. [Production split-pencil criterion](quarter-successor-split-pencil.md)
