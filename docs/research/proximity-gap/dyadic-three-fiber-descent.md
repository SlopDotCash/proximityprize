# Three completely split fibers on complex dyadic grids

Let \(N\) be a power of two, let \(A,B,C\) be disjoint sets of \(d\) complex \(N\)-th roots of unity, and put \(L_S(X)=\prod_{s\in S}(X-s)\). If \(L_A,L_B,L_C\) satisfy a nontrivial linear relation, **the odd part of \(d\) is at most nine**. Equivalently, a rational function of degree \(d\) with three totally split fibers of \(d\) distinct grid points can exist only at such a degree. A target Möbius change takes the three fiber values to zero, infinity and one. All three coefficients in the locator relation are nonzero by disjointness.

The proof gives a dichotomy at every \(d\ge11\). Either all three fibers lie in a coset of \(\mu_{N/2}\), or all three are globally antipodal and the rational function factors through \(X^2\). Both operations halve the grid size. The second also halves the degree. The result excludes a common complex realization of the three-fiber patterns of degrees \(268435454=2\cdot134217727\), \(268435455\), and \(268435457\). The existence of the corresponding layouts in individual named production fields remains open. [Finite-field quarter successor](quarter-successor-split-pencil.md) · [Production lifting limits](production-ratio-lifting.md)

## The two frequencies on the half-size grid

Write \(\zeta\) for a primitive \(N\)-th root and \(M=N/2,\ \theta=\zeta^2\). We identify sets of roots with exponent sets when discussing their parity. Suppose \(A,B\) are antipodally symmetric on the odd exponents. An odd antipodal pair with exponents \(a,a+M\) supplies the factor \(Y^2-\theta^a\), with \(a\) odd modulo \(M\); an even singleton with exponent \(2b\) supplies \(Y-\theta^b\). Thus on the even grid their ratio is exactly
\[
 R(Y)=\prod_{b\bmod M}(Y-\theta^b)^{u(b)}
      \prod_{a\ {\rm odd}\bmod M}(Y^2-\theta^a)^{q(a)} .
\]
Here \(u\) and \(q\) are signed indicators for the two supports and for their odd pairs. They take values \(0,1,-1\).

Suppose the ratio takes a common nonzero finite value at five sites \(Y=\theta^j\) with the five indices \(j\) of the same parity. Rotating all the original roots by \(\zeta^{-2}\) if necessary makes those indices even. Such a rotation preserves constancy and the antipodal structure. In \(\mathbb Q(\theta)\) use the automorphism \(\sigma(\theta)=-\theta\). The coefficients of the displayed ratio and its common value at these sites belong to this subfield. Since all five \(Y\)'s are fixed, \(R(Y)/\sigma(R)(Y)\) has one common value there. Define two antiperiodic functions on \(\mathbb Z/M\) by
\[
 v(b)=u(b)-u(b+M/2)\ \ (b\ {\rm odd}),\qquad
 w(a)=q(a)-q(a+M/2)\ \ (a\ {\rm odd})
\]
and put both functions equal to zero on even indices. Conjugation cancels the even-singleton factors with even \(b\); it swaps \(b\) with \(b+M/2\) and \(a\) with \(a+M/2\) in the remaining factors. At an even \(j\) we therefore have
\[
 \frac{R(\theta^j)}{\sigma(R)(\theta^j)}
 =\prod_{b\ {\rm odd}}(1-\theta^{b-j})^{v(b)}
  \prod_{a\ {\rm odd}}(1-\theta^{a-2j})^{w(a)} .
\]
The extracted monomials cancel because each antiperiodic exponent function sums to zero.

For a dyadic primitive root \(\theta\), an integral product of the factors \(1-\theta^i\) at odd exponents can be a root of unity only if the total exponent at each pair \(\{i,-i\}\) is zero. This follows by taking the logarithms of absolute values at all embeddings and using the nonvanishing character eigenvalues of the log-sine matrix. Applying it to the quotient of two of the last five expressions gives, for every \(i\),
\[
 F_j(i)=v(j+i)+v(j-i)+w(2j+i)+w(2j-i)
\]
independent of \(j\) among the five chosen sites. For even \(i\) all four terms are zero. [Primitive log-sine independence](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

Use the Fourier convention \(\widehat f(k)=\sum_i f(i)\theta^{-ki}\). At frequency \(k\) the transform of \(F_j\) equals
\[
    2\operatorname{Re}\bigl(\widehat v(k)\,\theta^{kj}
                         +\widehat w(k)\,\theta^{2kj}\bigr).
\]
At even \(k\) both transforms vanish by antiperiodicity. For odd \(k\), the five values \(z=\theta^{kj}\) are distinct since \(k\) is invertible modulo \(M\). Write \(a=\widehat v(k)\), \(b=\widehat w(k)\), and \(h\) for their common displayed real value. Multiplying by \(z^2\) shows that the five points are roots of
\[
             bZ^4+aZ^3-hZ^2+\overline a Z+\overline b .
\]
A quartic with five distinct roots vanishes identically. [Lean five-root lemma](../../../ArkLib/Research/ProximityGap/Frontier/DyadicFiveCenterFourier.lean) Thus \(b=a=0\) at every odd frequency as well. Fourier inversion gives \(v=w=0\). In particular
\[
                      q(a)=q(a+M/2)\qquad(a\ {\rm odd}).
\]
The positive and negative odd-pair labels are disjoint, so this symmetry holds separately for \(A\) and \(B\). On the original grid each nonempty orbit of these pairs has **four** distinct physical odd roots. Five test sites at one residue class modulo four therefore force the odd roots of both locators to be unions of quarter-rotation orbits.

## Descent in grid and degree

Any one of the three full fibers can be the test set, since the ratio of the other two locators has one constant value on it. By the three-center parity lemma, three tests of one parity force both of the other supports to be antipodally symmetric on the opposite parity. If a test set has three points of each parity, both other supports are globally antipodal. Their monic locators are then polynomials in \(X^2\), as is their nonzero linear combination giving the third locator. All three support sets are globally antipodal. Squaring the grid gives three disjoint completely split fibers of degree \(d/2\) on \(\mu_{N/2}\). [Three-center parity lemma](production-ratio-lifting.md#the-parity-constraint-in-the-complex-field)

In the remaining case each of the three sets has at most two elements of its minority parity. Rotate by \(\zeta\) if necessary so that two sets have an even majority. Every set has at least one *other* even-majority test set. Therefore each is antipodally symmetric on odd exponents. If the third set has an odd majority, it has at least three odd points and forces the other two to be antipodally symmetric on even exponents also. We again have two globally antipodal locators and the degree-halving case applies.

It remains that all three sets have an even majority. Each then has at least \(d-2\ge9\) even exponents. At least five of these are congruent modulo four. Apply the two-frequency argument with any of the three sets as tester. It forces each of the other two to have its odd sites in orbits of size four. Each has at most two odd sites, so neither has any. Varying the tester proves all three sets are entirely even. Restriction to the half-size grid now preserves the degree and the original locator relation.

If the odd part of \(d\) is at least eleven, every subsequent degree is at least eleven. Either reduction can be repeated, but the strict grid-size decreases must eventually give fewer than \(3d\) points for the three disjoint fibers. This proves the theorem. The argument also applies in any characteristic-zero field after specialization of its roots of unity to a complex primitive root: linear dependence of the three monic locator coefficient vectors is determined by their minors in the dyadic cyclotomic subfield.

## Finite-field consequences and bounds

On the order-128 subgroup at each named prime every individual locator-ratio comparison lifts to the complex numbers. The theorem therefore excludes three disjoint full fibers at every degree with odd part at least eleven there. On the order-256 subgroup, a *common labeled layout* producing the three full fibers in both named fields lifts to characteristic zero and is likewise excluded. The latter conclusion permits each field to have its own scalar fiber values. [Order-128 individual transfer](mu128-unit-ellipsoid-transfer.md) · [Order-256 joint transfer](mu256-joint-transfer.md)

For a separate explicit largeness condition, let \(p\) be the characteristic of a field containing a primitive \(N\)-th root. If
\[
                        p>2^{(2d+1)N/2},
\]
every two-site comparison of two \(d\)-root locators on this grid lifts. After clearing denominators its difference is an algebraic integer. In each of the \(N/2\) complex embeddings, the triangle inequality bounds its absolute value by \(2^{2d+1}\). If nonzero its absolute norm is at most the displayed bound and cannot have a prime factor \(p\) above it. Thus the same no-three-fiber conclusion holds for individual prime characteristics in this range. The designated production primes do not satisfy this sufficient bound.
