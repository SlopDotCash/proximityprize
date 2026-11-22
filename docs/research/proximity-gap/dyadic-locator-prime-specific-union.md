# Product-conditioned locator bounds at the two named primes

At length $2^{30}$, rate $1/16$ and **83,886,079 agreements**, the first named prime admits at most **840,756,069** words from the family below. The second named prime admits at most **2,069,043,626** even after adding the entire order-256 degree-nine class. The margins below their designated budgets $2^{30}$ and $2^{31}$ are **232,985,755** and **78,440,022** words.

On both fields take every degree on the dyadic quotients of orders $1$ through $128$, except for order-128 degree nine. On the order-256 quotient take degrees 0 through 8, degree 18 with at most eight unpaired roots, and all degrees 19 through 256. Also take degree nine on the order-256 quotient of the second field. For each quotient order $M$ and degree $m$, choose any one fixed monic numerator $P$ and nonzero multiplier $H$ of degree at most $h-1$, where $h=2^{30}/M$. The bounds are uniform over the common received word and these choices. Projection onto one coordinate extends them to repetitions of the scalar candidates at any positive interleaving width. [Locator family and incidence bounds](dyadic-locator-degree-caps.md#locators-on-every-dyadic-quotient-through-order-128)

## The extra factor of four in the integer determinant

Let $T,T'$ be supports of the same size and prescribed product in a cyclic group of even order $M$, written as exponent sets for its fixed generator. In $\mathbb Z[X]$ put $F(X)=\sum_{j\in T} X^j-\sum_{j\in T'} X^j$. Then $F(1)=0$, and $F'(1)=\sum_{j\in T}j-\sum_{j\in T'}j$ is a multiple of $M$. For a dyadic divisor $D\ge4$ of $M$, set $R_D=\mathbb Z[X]/(X^{D/2}+1)$. In this ring
$$
  2=(1-X)(1+X+\cdots+X^{D/2-1}).
$$
Expanding $F$ in powers of $X-1$, its constant term is zero and its linear coefficient is even. Thus $F$ is a multiple of $(X-1)^2$ in $R_D$. The determinant of multiplication by $X-1$ on this free integer module has absolute value $\Phi_D(1)=2$, by the characteristic polynomial $X^{D/2}+1$ of multiplication by $X$. Multiplicativity of the determinant gives $4\mid\det(F)$. Lean also derives the squared divisor directly from equal support sizes and equal products, and proves the factor four for an integer-valued multiplicative norm with even value on $X-1$. [Formal ramification and norm lemmas](../../../ArkLib/Research/ProximityGap/Frontier/LocatorProductRamification.lean)

Write the residue of $F$ in the usual power basis of $R_D$, and let $E$ be its sum of squared coefficients. Distinct folded vectors give a nonzero residue and hence a nonzero determinant by irreducibility over $\mathbb Q$. The multiplication matrix has rows of squared length $E$, so $|\det(F)|\le E^{D/4}$. At $c$ distinct prescribed roots of $\Phi_D$ modulo $p$, the difference vanishes. The mod-$p$ rank drops by at least $c$, giving $p^c\mid\det(F)$. As the named primes are odd, a nonzero residue must satisfy
$$
                       4p^c\le E^{D/4}.
$$
The coefficient sum of the folded difference has the parity of $F(1)=0$: folding only changes signs and adds coefficients. Since $a^2\equiv a\bmod2$ for integers, $E$ is even. With $p$ equal to the first or second named prime, respectively, these tests give the following least possible positive squared distances. [Integer determinant and modular-rank proof](dyadic-locator-degree-caps.md#recovering-integral-identities-from-finite-field-rank)

| Conductor $D$ | Number $c$ of prescribed odd frequencies | First prime | Second prime |
|---:|---:|---:|---:|
| 128 | 1 | 34 | 34 |
| 256 | 2 | 32 | 34 |

Indeed both primes exceed $2^{158}$, so $32^{32}<4p$. The second exceeds $2^{159}$, giving $32^{64}<4p^2$ as well. At conductor 256 on the first prime, $30^{64}<4p^2\le32^{64}$. The certificate below checks each adjacent integer threshold directly.

## Which locator constraints supply the distances

The identity $YQ_T(Y)=P(Y)-L_T(Y)$ fixes the root product at every degree. On fixing the unpaired roots, write the full pairs as $\{u,-u\}$ and their labels as $u^2$. Their product contribution is $(-1)^q\prod u^2$, where $q$ is the number of pairs. Thus the $q$ labels in the half-order group again have a prescribed product. Whenever the second power sum of the original roots is known, the label sum is determined by subtracting the singleton contributions and dividing by two.

- At order 128, degrees 10 and 11 prescribe the first power sum. Use $D=128,c=1$ in the fixed-sum, fixed-product completion count $J_\times$.
- At order 256 and degree 19, only frequencies 1 and 2 are prescribed. For a signed imbalance on the four-root blocks $\{g^j,g^{j+64},g^{j+128},g^{j+192}\}$, the difference of imbalance vectors is exactly the power-basis residue of $F$ at conductor 128. The second power sum supplies one root there. Use distance 34 for the imbalance vectors and the order-128 completions. The primitive phases continue to use the independently verified five-term sum property. [Phase and imbalance argument](dyadic-locator-degree-caps.md#degree-19-on-the-order-256-quotient)
- At order 256 and degrees 20 and 21, frequencies 1 and 3 give two distinct primitive evaluation roots. Pair restoration uses the second moment and the already fixed root product. Thus the primitive signed-vector packing uses the second row of the distance table while the completions use its first row.
- At order 256 and degree 22, the three prescribed primitive odd frequencies already force equality of the primitive orientation by the full integral lift. At most eleven full pairs remain. Their fixed-sum, fixed-product count uses $D=128,c=1$. The integral lifting bounds also apply without change from degree 12 at order 128 and degree 23 at order 256. [Integral-lift ranges](dyadic-locator-degree-caps.md#dimensions-where-the-determinant-can-vanish-modulo-the-prime)

## Counts in a common received ball

The higher-degree rows count eligible supports before imposing agreements. The low-degree and degree-18 rows use the prescribed-product bound on the number of supports concentrated in the baseline fibers, together with the exact multiplicity caps for a fresh locator signature. The same numerator and multiplier are used for each degree-18 weight at a given quotient. [Baseline occupancy calculation](locator-baseline-occupancy.md) · [Full-field signature censuses](antipodal-locator-fresh-energy.md)

| Quotient | Degrees | First prime | Second prime |
|---|---|---:|---:|
| 1 through 64, dyadic | All | 165,240 | 165,240 |
| 128 | 0 through 8 | 13,161,160 | 13,161,160 |
| 128 | 10 through 128 | 481,856 | 481,856 |
| 256 | 0 through 8 | 48,151,877 | 48,151,877 |
| 256 | 9 | Outside this family | 1,332,411,487 |
| 256 | 18, at most eight unpaired roots | 617,033,304 | 617,033,304 |
| 256 | 19 | 48,952,114 | 48,952,114 |
| 256 | 20 | 9,150,513 | 961,555 |
| 256 | 21 | 103,415,663 | 7,480,691 |
| 256 | 22 | 238,266 | 238,266 |
| 256 | 23 through 256 | 6,076 | 6,076 |
| | **Sum** | **840,756,069** | **2,069,043,626** |

Varying the agreement count in the occupancy calculation also keeps the indicated families within budget at **82,747,292 agreements on the first prime** and **83,482,060 on the second**. The respective union bounds there are 1,073,741,712 and 2,147,483,436. At one fewer agreement the calculated bounds are 1,073,741,992 and 2,147,483,650. These integer crossings certify sufficient agreement thresholds for the two different families.

The unrestricted first-failure upper bounds on the two named domains are still **989,855,734** and **989,855,741 errors**, respectively, from order-128 degree-nine witnesses. This table bounds the stated collections of locators around arbitrary centers. [Unrestricted witnesses](sixteenth-locator-union.md)

Run the [integer verifier](../../../scripts/probes/probe_dyadic_locator_prime_specific_union.py) with Python 3. It checks the conductor thresholds, all degree charges and the two sums. At conductors four and eight it also checks the factor of four against exact multiplication determinants for all 682 distinct equal-size, equal-product pairs on the order-eight group. Both conductors exhibit determinant four, and dropping the prescribed product admits determinant two. The occupancy and finite-field signature checks can be run independently with the commands in the linked notes.

~~~sh
python3 -B scripts/probes/probe_dyadic_locator_prime_specific_union.py
~~~
