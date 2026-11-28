# Exclusion of three full seven-point fibers on every complex dyadic grid

A degree-seven rational function cannot have three disjoint full seven-point fibers on the complex dyadic roots of unity. Together with the two-frequency descent and the degree-nine result, **the odd part of any degree with three full fibers is at most five**. The finite-field transfer conditions for the general descent continue to apply. [Two-frequency descent](dyadic-three-fiber-descent.md) · [Degree-nine descent](dyadic-nine-fiber-descent.md)

## Shell equations

Take a minimal dyadic grid of order \(N\) supporting a counterexample. As in the general descent, rotate so each color's minority odd sites form either one antipodal pair or the empty set, and the majority is even. Put \(\theta=\zeta_N^2\), \(M=N/2\). A color with an odd pair has label \(t_i=\theta^{a_i}\), \(a_i\) odd, equal to the square of either member. Write \(t_i=0\) if that pair is absent. Two nonzero labels are distinct. We call the indices \(j\) of the remaining sites \(\theta^j\) even or odd according to their parity modulo two. Let \(\mathcal S_i\) be the members of color \(i\) in one such parity class, with sum \(S_i\); write \(V_i\) for the sum of its members in the opposite class.

We use the following equations, which also allow one of the *other* labels \(t_j,t_k\) to be zero. If \(t_j\ne t_k\) and \(\mathcal S_i\) has three or four members, put
\[
 q_{jk}=\frac{t_j-t_k}{\bar t_j-\bar t_k},\qquad
 z_i=\begin{cases}q_{jk}/\prod\mathcal S_i&|\mathcal S_i|=3,\\0&|\mathcal S_i|=4.\end{cases}
\]
For four members one also has \(\prod\mathcal S_i=q_{jk}\). The leading and cubic coefficients of the Fourier quartic give
\[
                 \bar V_j-\bar V_k=-(\bar t_j-\bar t_k)(S_i+z_i).             \tag{1}
\]
Here \(q_{jk}=-t_jt_k\) with two nonzero labels and \(q_{jk}=t_j^2\) when only \(t_j\ne0\). Thus a nonzero \(z_i\) is a dyadic root. For four tests the sum \(S_i+z_i\) has four terms; for three it has the three actual roots and the fourth, virtual, root. In either case it vanishes modulo \(1-\theta\). In particular the opposite-class counts of the other colors have the same parity. If \(|\mathcal S_i|\ge5\), the higher-degree argument already forces both other labels to vanish.

Whenever \(t_i\ne0\), evaluation on its two original odd sites gives the independent reflection equation
\[
                   S_j-S_k=-t_i(\bar V_j-\bar V_k).                         \tag{2}
\]
The odd-pair factors in the other locators cancel whether present or absent. The remaining displacements are odd primitive exponents, and their signed exponent counts give (2) exactly as at degree nine. [Four-test coefficient identity](dyadic-three-fiber-descent.md#the-two-frequencies-on-the-half-size-grid) · [Odd-pair reflection](dyadic-nine-fiber-descent.md#a-reflection-obstruction-for-three-odd-pairs)

We compare sums of dyadic roots using the rational basis \(1,\theta,\ldots,\theta^{M/2-1}\). A multiset sum has a unique remainder after deleting antipodal pairs. For differences of sums of disjoint sets, the total absolute coefficient weight equals the sum of the sizes of their individual remainders: opposite roots in different sets reinforce in a difference. In particular two disjoint odd sets cannot have equal sums. If no top odd pair occurs then the grid halves, contrary to minimality. It remains to exclude one, two and three nonzero labels.

## One nonzero label

Suppose only \(t_i\ne0\). Each other color has seven half-grid sites; it must split four and three between the two parity classes, since five on one side would force \(t_i=0\). Applying (1) to both four-site classes shows that all three colors have the same count parity in either fixed class. Thus the two seven-site colors \(j,k\) have the same four-site class. Call it \(H\), and call the other class \(L\), writing \(H_s,L_s\) for the corresponding sums. Color \(i\) has five half-grid sites, evenly many in \(H\).

Test the ratio for \(j,k\) on the even sites of \(i\). The locators for \(j,k\) have all their roots on the half grid. Three tests in \(H\) would force their three light roots to be antipodally paired by the ordinary three-center lemma. Hence \(i\) has at most two sites in \(H\) and at least three in \(L\). Those three force the other colors' heavy quartets to be antipodally paired, giving \(H_j=H_k=0\). Testing (1) on the four sites in \(H\) of color \(j\) now gives \(L_i=L_k\), impossible for disjoint odd sets. [Three-center parity lemma](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

## Three nonzero labels

For each color set \(\delta_s=\|H_s\|-\|L_s\|\) using the coefficient absolute-value norm in the dyadic power basis. Each \(\delta_s\) is odd, since its even-grid support has five sites. The reflection equation (2) at each odd pair gives \(\delta_j+\delta_k=0\) for the other two colors, because those colors have disjoint supports. The three equations force \(\delta_s=0\) for every color. [Reflection and norm argument](dyadic-nine-fiber-descent.md#a-reflection-obstruction-for-three-odd-pairs)

## Two nonzero labels

Use \(i\) for the color without an odd pair. Its seven half-grid sites split into a heavy class \(H\) of size four and a light class \(L\) of size three. The other colors \(j,k\) have five half-grid sites and no five in a single class. Testing (1) from each of \(j,k\) on three or four sites shows that their heavy counts have the parity of the heavy count of \(i\). Each is therefore two or four. Put \(r=t_k/t_j\ne1\).

For any fixed class denote its sums by \(S_s\) and the opposite sums by \(V_s\). Applying the two reflection equations (2) from \(j,k\), and then (1) from \(i\), gives
\[
                        t_j(S_j+z)=t_k(S_k+z),                              \tag{4}
\]
with \(z=0\) in the heavy class, and \(z\prod\mathcal L_i=-t_jt_k\) in the light class. Indeed subtracting the conjugate reflection equations gives
\(\bar V_j-\bar V_k=\bar t_j S_k-\bar t_k S_j-(\bar t_j-\bar t_k)S_i\), and compares directly with (1). We write \(K_H=t_jH_j=t_kH_k\) and \(K_L=t_j(L_j+z)=t_k(L_k+z)\), where from now on \(z\) is the light virtual root. Also whenever color \(j\) has three or four sites in the chosen class, comparison of (1) from its tests with (2) from its odd pair gives
\[
 S_k-S_i=(t_j/t_k)(S_j+z_j),\qquad
 q_{ki}=t_k^2,                                                              \tag{5}
\]
and likewise with \(j,k\) exchanged.

**Both heavy counts equal four.** Testing (1) from \(j\) gives \(\bar L_k-\bar L_i=-K_H/(t_jt_k)\); testing from \(k\) gives the same value for \(\bar L_j-\bar L_i\). The light singletons are disjoint, contradiction.

**One heavy count is four.** Label that color \(j\); color \(k\) has two. Then \(K_H\) is the sum of two roots. If zero, (1) from \(j\) gives \(L_i=L_k\), impossible for disjoint odd sets. Otherwise \(\bar L_i-\bar L_k=K_H/(t_jt_k)\) has absolute coefficient weight two. The disjoint light triples of \(i,k\) must each contain an antipodal pair. Write \(\ell_i,\ell_k\) for their remaining roots, and \(\ell_j\) for the light singleton. By (4),
\[
                      t_j(\ell_j+z)=t_k(\ell_k+z).
\]
This common sum is nonzero, since otherwise the two distinct singletons would both be \(-z\). The two unsimplified root pairs must be equal as multisets; since \(t_j\ne t_k\) their matching crosses. It gives \(\ell_j=rz,\ \ell_k=z/r\). Color \(k\)'s virtual light root \(z_k\) now gives by (5)
\(\ell_i=rz-z-rz_k\). For these three terms to sum to a single root there must be an antipodal cancellation. The equality \(rz=z\) is impossible. If \(z=-rz_k\), then \(\ell_i=\ell_j\), impossible. Thus \(z=z_k\), \(\ell_i=-z\). Let the internal pairs of \(i,k\) be \(\{\pm b\},\{\pm c\}\). Their product equations \(z\prod\mathcal L_i=-t_jt_k\) and \(z\prod\mathcal L_k=t_j^2\) give \(z^2 b^2=z^2 c^2=-t_jt_k\), making the pairs equal across disjoint colors.

**Both heavy counts equal two.** All three light sets are triples. Put \(U=L_i+z\). Equations (4)–(5) yield
\[
                        z_j=z-rU,\qquad z_k=z-U/r.                           \tag{6}
\]
Both right sides have absolute value one. If \(r\ne-1\), comparing squared absolute values shows \(U/z\) is real, and then it is either zero or \(r+r^{-1}\). If \(r=-1\), the unit root \(z_j=2z+L_i\) is a sum of five dyadic roots. To reduce to one root two pairs must cancel. At most one pair can use a displayed \(z\), since the three actual roots are distinct. Hence \(\mathcal L_i\) contains \(-z\) and one internal pair, and \(U=0\).

If \(U=0\), the light equation (1) at \(i\) gives \(H_j=H_k\); (4) then forces both to be zero. Equation (2) gives \(H_i=t_j(\bar L_k+\bar z)=t_k(\bar L_j+\bar z)\), which is nonzero since otherwise disjoint odd light sets would have the same sum \(-z\). If all four heavy roots of \(i\) are unpaired, their set equals each of the two corresponding four-root multisets. Their product is then \(t_j^2=t_k^2\) by \(z_j=z_k=z\) and the light product equations. Thus \(t_k=-t_j\), and the two completed light sets are negatives of each other. This forces \(-z\) in the light sets of both \(j,k\), contradiction. Otherwise \(H_i\) reduces to two roots. Each completed light set of \(j,k\) must cancel a pair internally to its light triple, since \(-z\in\mathcal L_i\). Calling the remaining roots \(\ell_j,\ell_k\), (4) gives \(\ell_j=rz,\ell_k=z/r\) by the same crossed matching. The product equations for \(j,k\) then give the same squared value \(-t_jt_k/z^2\) for their two internal pairs. Again their root sets overlap.

Finally suppose \(U=z(r+r^{-1})\ne0\). Then \(r\) has dyadic order at least eight. The four roots in \(L_i+z\) reduce to the two distinct nonopposite roots \(zr,z/r\). Neither equals \(z\). Hence the canceling pair uses \(z\) itself and \(\mathcal L_i=\{zr,z/r,-z\}\). Equation (6) gives \(z_j=-zr^2,\ z_k=-z/r^2\). The corresponding product equations give
\[
                   z\prod\mathcal L_j=-t_j^2,\qquad
                   z\prod\mathcal L_k=-t_k^2.
\]
After scaling the completed multisets by \(t_j,t_k\) respectively, their sums coincide by (4) but their products \(-t_j^6,-t_k^6\) differ because the order of \(r\) is at least eight. Both multisets must cancel an antipodal pair. Since \(-z\in\mathcal L_i\), both cancellations are internal to the actual light triples of \(j,k\). The crossed matching now gives their remaining roots as \(rz,z/r\), both already in \(\mathcal L_i\). This final contradiction excludes the minimal grid and proves the theorem.
