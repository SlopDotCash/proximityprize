# A quarter-rate attack with four noncollinear vector cubics

At the second named prime and length $n=2^{30}$, one quarter-rate received pair has at least **2,214,592,518 distinct MCA-bad scalars at 553,648,129 errors**. This lowers the previous four-head ceiling by 11,983,725 errors. The scalar budget is 2,147,483,648. Lean verifies the mass throughout dimensions 268,435,456 to 520,093,694 and at every positive interleaving width. [Noncollinear quarter-rate theorem](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimePlanarQuartet.lean) · [Finite-field certificate](../../../scripts/probes/probe_second_prime_four_cubics.py)

Write $s=2^{26}$, $k=4s$, $w=g^s$ for the named generator, and $t=X^s$. For an exponent set $A$, write $L_A(t)=\prod_{j\in A}(t-w^j)$. Start with four polynomial pairs of degree at most three. Head zero is the zero pair. Head one is $(L_{0,2,4},0)$. Head two is $(bL_{5,13},(t-w^6)L_{5,13})$ with $b=L_{0,2,4}(w^6)/L_{5,13}(w^6)$. Head three is the cubic in each entry that agrees with head two at exponents 8, 10 and 12 and with head one at exponent 15. In each pair replace the second entry by the sum of its two entries, calling the resulting coordinates $U_i,V_i$.

| Head pair | Equality exponents |
|---|---|
| 0, 1 | 0, 2, 4 |
| 0, 2 | 5, 13 |
| 0, 3 | 14 |
| 1, 2 | 6 |
| 1, 3 | 7, 15 |
| 2, 3 | 8, 10, 12 |

Direct field evaluation gives exactly these twelve double sites. It also checks that every two distinct values have distinct second coordinates, and that any three distinct planar values at a single site are noncollinear. Each quotient fiber has $s$ production coordinates.

Receive the matching double head on each of the twelve pair fibers. The four private fibers have exponents 1, 3, 9, 11. In the first two select $s/4-1$ common roots, and in the other two select $s/4$ each. Their locator $J$ has degree $s-2$. Assign the remaining sites of the four private fibers to heads 0, 1, 2, 3 respectively. Each defining core now includes the common roots, six complete pair fibers, and at least $3s/4$ private sites. The minimum core size is $C=31s/4-2=520093694$.

For parameters $a,b$ give head $i$ the polynomial pair
\[
 (a J U_i(X^s)+ b X J V_i(X^s),\quad J V_i(X^s)).
\]
Both entries have degree less than $k$. The received entries at each site are those of its owner. At every nonroot $x$, a foreign head $i$ whose quotient value differs from its owner $h$ gives the label
\[
 a\frac{U_h(x^s)-U_i(x^s)}{V_i(x^s)-V_h(x^s)}-b x .
\]
The coefficient pairs distinguish different sites by their second coordinate, and distinguish foreign values at a common site by the determinant check. Two different coefficient pairs exclude one proper linear condition on $(a,b)$. Fewer than $p$ such conditions suffice to avoid all collisions simultaneously. Every chosen label agrees on its head's core plus the foreign site. A simultaneous fit to both rows would have to equal the head on every coordinate by polynomial uniqueness on its core, contradicting the second-row mismatch at the foreign site.

The twelve pair fibers give $24s$ labels. The $3s+2$ private sites give $9s+6$ more. The total is $33s+6$, at $n-C-1$ errors. The same attack works at every positive interleaving width by MCA stability. The unrestricted first failing count still needs a matching lower bound.
