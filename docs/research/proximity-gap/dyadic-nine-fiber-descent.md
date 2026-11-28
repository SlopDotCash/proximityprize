# Exclusion of three full nine-point fibers on every complex dyadic grid

On a complex dyadic root grid \(\mu_N\), a rational function cannot have three disjoint full fibers of size nine at degree nine. Together with the descent for higher degrees, this bounds the odd part of any degree admitting such three full fibers by **seven**. [Higher-degree descent and finite-field scope](dyadic-three-fiber-descent.md)

Suppose a nine-fiber pencil exists, with label sets indexed by \(i=1,2,3\), and take the smallest possible dyadic grid. Use the parity reduction and the two-frequency Fourier equations of the higher-degree proof. An odd-degree full pencil cannot be globally antipodal. Rotate the grid so all three colors have an even majority and at most two odd sites, antipodally paired in each color. If some color has no odd site, its nine even sites include five in one class modulo four. The two-frequency lemma forces the odd sites of the other colors into orbits of size four, so they also have none. The pencil descends to a smaller grid. Thus in a minimal example each color has seven even sites and one odd antipodal pair. The seven even sites must split four and three between the two classes modulo four, since a five-site class gives the same contradiction.

## A reflection obstruction for three odd pairs

This last configuration is impossible at every odd degree, independently of the distribution of the even sites modulo four. Put \(M=N/2\) and \(\theta=\zeta_N^2\). Color \(i\)'s top odd pair is \(x_i,-x_i\) with \(t_i=x_i^2=\theta^{a_i}\), \(a_i\) odd. Write \(H_i,L_i\) for the sums of its remaining roots \(\theta^b\) at even and odd \(b\), respectively.

For distinct colors \(i,j,k\), compare the locator ratio of \(j,k\) at \(x_i,-x_i\). The factors from the other two odd pairs are polynomials in \(X^2\) and cancel. The ordinary root \(\theta^b\) contributes, up to sign, the factor
\[
                 (1-\zeta_N^{2b-a_i})/(1+\zeta_N^{2b-a_i}).
\]
Its displacement is odd. Write \(s(b)\) for the signed difference of the remaining supports of \(j,k\). Primitive-unit independence at the full grid says the total exponents at each pair of opposite displacements sum to zero. Here the two displacements correspond to \(b\) and \(a_i-b\), giving
\[
 s(b)-s(b+M/2)+s(a_i-b)-s(a_i-b+M/2)=0 .
\]
Multiply by \(\theta^b\) and sum over even \(b\). Reflection in the odd index \(a_i\) swaps parity, so
\[
                       H_j-H_k=-t_i(\bar L_j-\bar L_k).
\]
The same identity holds whenever color \(i\) has an odd pair and the other colors' odd sites are unions of antipodal pairs, including the empty set. [Primitive-unit independence](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

Use \(\|w\|\) for the sum of absolute values of the rational coefficients of \(w\) in the basis \(1,\theta,\ldots,\theta^{M/2-1}\). Multiplication by a dyadic root of the half grid and complex conjugation are signed permutations of this basis. For an ordinary site set, its sum has norm equal to its cardinality after deleting internal antipodal pairs. For two disjoint site sets the norm of the difference of their sums equals the sum of the two norms: a cross-antipodal pair places the two contributions at the same basis element with the same sign in the difference. Thus the reflection identity gives
\[
        \delta_j+\delta_k=0,\qquad \delta_s=\|H_s\|-\|L_s\|.
\]
Having a top odd pair in each of the three colors gives all three equations. They force all three integers \(\delta_s\) to vanish. But \(\delta_s\) has the parity of the remaining-site count \(d-2\), which is odd. This proves the obstruction and excludes degree nine. The same calculation will exclude three top pairs in the degree-seven proof.
