# Dyadic parity excludes the punctured half-rate four-list over the complex numbers

Let $n=4h\ge64$ be a power of two, and remove one site from $\mu_n$. Over the complex numbers no received word on these $n-1$ sites lies within $h+1$ errors of four distinct scalar polynomials of degree at most $2h-2$. The exclusion holds for the order-64 subgroup at both named primes as well. At the first named prime's production length $2^{30}$, the endpoint equivalence still requires a finite-field argument for the protected ratios. [Punctured list and operational endpoint](first-prime-punctured-four-list.md)

## Six protected divisor signatures

Write $U_i$ for the sites where only head $i$ misses the received word. Counting the intersections of the four error sets gives the three patterns in the following table. The marked sites are the remaining sites, including the puncture. In every row there are two rational functions $F,G$ of degree $h-1$. Each fiber displayed is complete and simple. Adjoining a letter to a private class denotes the union with that one marked site. The three entries in each fiber column give the zeros, poles, and unit fiber, in this order. [Four-fiber equations and construction](four-fiber-quadratic-characters.md)

| Shape | Private populations $|U_0|,|U_1|,|U_2|,|U_3|$ | Marked sites | Fibers of $F$ | Fibers of $G$ |
|---|---|---:|---|---|
| Six doubles | $h-2,h-2,h-2,h-2$ | 8 | $U_0+b, U_1+d, U_2+f$ | $U_0+a, U_1+c, U_3+f$ |
| Five doubles | $h-2,h-2,h-1,h-1$ | 6 | $U_0+b, U_1+d, U_2$ | $U_0+a, U_1+c, U_3$ |
| One triple | $h-1,h-2,h-1,h-1$ | 5 | $U_0, U_1+d, U_2$ | $U_0, U_1+c, U_3$ |

For either pencil with fibers $(Z,P,V)$, the divisor signatures of the pencil, the pencil minus one, and the pencil divided by the pencil minus one are $1_Z-1_P$, $1_V-1_P$, and $1_Z-1_V$, respectively. All are differences of disjoint simple locator indicators. The corresponding protected ratios, constant on the indicated private class, are

| Center class | Protected ratios |
|---|---|
| $U_0$ | $F-1$ and $G-1$ |
| $U_1$ | $F/(F-1)$ and $G/(G-1)$ |
| $U_2$ | $F$ |
| $U_3$ | $G$ |

At a pole the quotient of a pencil by that pencil minus one takes the value 1. Thus all of these protected comparisons are between finite nonzero values of ratios of disjoint locators. If a center class contains at least three sites on one exponent parity, the dyadic three-center theorem makes every one of its signatures invariant under the antipode on the *other* parity. Call such a center class heavy on its parity. [Three-center theorem](quarter-dyadic-parity.md#three-equal-ratios-in-one-parity-class)

## The odd class

Both parities have $2h$ sites. If one had at most one heavy private class, it could contain at most $(h-1)+3\cdot2+8=h+13<2h$ sites. Every private class also has at least $h-2>4$ sites altogether and is consequently heavy somewhere. We can therefore partition the four private classes into two complementary pairs, each heavy on its own parity. To do so, include in the first pair every class that is not heavy on the second parity. At most two such classes exist, and the first parity has enough heavy classes to fill that pair. Up to exchanging parities, the possible splits are $01\mid23$, $02\mid13$, and $03\mid12$.

For each split the table gives one class distinguished from every other class by the signatures of the first pair, and also distinguished from every other class by those of its complementary pair.

| Shape | $01\mid23$ | $02\mid13$ | $03\mid12$ |
|---|---|---|---|
| Six doubles | $\{a\}$ | $\{f\}$ | $\{f\}$ |
| Five doubles | $\{a\}$ | $U_2$ | $U_2$ |
| One triple | $U_0$ | $U_0$ | $U_0$ |

Each entry follows by substituting the zero, pole and unit sets above. For instance in the six-double shape both $F-1$ and $G-1$ have a zero at $f$, and both $F/(F-1)$ and $G/(G-1)$ have a pole there. No other site has either pair of features. Thus when 0 and 1 belong to opposite heavy pairs, each pair isolates $f$. In the five-double and triple rows the private populations selected by the table equal $h-1$. Every entry therefore has odd total cardinality.

On either exponent parity the signatures from the opposite heavy pair are antipodally invariant. Each selected class is consequently a union of complete antipodal pairs across the domain. Its cardinality is even, contradicting the table.

The Lean development verifies the protected-signature table for all site types, the existence of complementary heavy pairs, both population inequalities, and the equality between the two antipodal membership indicators for the isolated class. The theorem `no_protected_list` combines them under the displayed signature and population hypotheses. The reduction from four polynomials to the three pencil patterns and the passage from complex locator comparisons to those hypotheses use the cited written proofs. [Lean parity obstruction](../../../ArkLib/Research/ProximityGap/Frontier/HalfFourFiberParity.lean)

## Finite fields

At $n=64$ an original named-field punctured list would supply the same finite protected ratio comparisons, with degree $15$ locators. The verified order-64 unit calculation transfers the comparisons individually to the complex cyclotomic field. The parity argument applies to the original exponents and gives the same contradiction. No compatible global lift of the two finite-field pencils is needed. [Order-64 unit transfer](mu64-unit-lattice-transfer.md)

More generally, a sufficient uniform transfer condition for a splitting prime at length $n$ is $p>2^{(2h-1)n/2}$. Cross-multiplication of one pairwise comparison of a protected locator ratio gives a difference of two products of $2(h-1)$ root differences. Each conjugate of this difference has absolute value at most $2^{2h-1}$. A nonzero integer norm therefore has absolute value at most $2^{(2h-1)n/2}$, and cannot be divisible by such a prime. This bound is much larger than the production prime at length $2^{30}$.

### A requirement at the first named production endpoint

If a received pair actually exceeds the sponsor budget at $h+1=268435457$ errors, then the punctured-list equivalence supplies the private sets and marks on the named subgroup. Fix a compatible primitive complex root and lift just the six *monic locator ratios* to its cyclotomic field. Their evaluations at the tested sites have no denominator divisible by the chosen splitting prime. For at least one protected ratio, **at least 44,739,242 different cyclotomic values must reduce to the same named-field element**. This is a necessary condition on a finite-field attack and uses no assumption that the site sets lift to a characteristic-zero list.

Indeed set $L=89478483$ and repeat the heavy-set counting proof with this threshold. Each parity has at least two classes of size at least $L$, since $(h-1)+3(L-1)+8<2h$, and each private class has size at least $L$ on one parity, since $h-2>2(L-1)$. The same nine-cell table shows that at least one of the associated divisor signatures changes on an antipodal pair. The dyadic three-center theorem then prevents its complex ratio from taking any one value on three sites of that large private class in that parity. At least $\lceil L/2\rceil=44739242$ distinct complex values occur. All original finite-field values coincide because the ratio is protected on that private class. The Lean module checks the production threshold and the final fiber count.
