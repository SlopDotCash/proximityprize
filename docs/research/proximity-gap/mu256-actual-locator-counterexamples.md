# Degree-62 locator ratios agree at four named-field sites and split over the complex numbers

For **each named prime** there are disjoint 62-element sets $P,Q$ of exponents in $\mathbb Z/256$ and four distinct even exponents outside them at which the ratio $L_P/L_Q$ has the same finite-field value. The corresponding ratio on the complex roots takes two distinct values on the four sites. On the odd exponents the antipode changes membership in these supports. The two primes use different examples. [Literal supports and Lean proof](../../../ArkLib/Research/ProximityGap/Frontier/Order256LocatorCounterexamples.lean)

| Named prime field | Four centers | Ratios modulo 257, in center order | Nonzero constant in the integer remainder | Odd support sites whose antipodes leave that support |
| --- | --- | --- | ---: | ---: |
| First | $2,4,252,254$ | $137,210,210,137$ | $-3601468257152$ | 58 |
| Second | $4,10,246,252$ | $124,36,36,124$ | $-18117040$ | 60 |

Write $L_S(T)=\prod_{j\in S}(T-z^j)$. The named-field generator $z$ has order 256. Kernel evaluation checks every listed degree, disjointness, nonzero denominator and all four equalities $L_P(z^i)=vL_Q(z^i)$. The common values are $188148678191796610178779171843413814268811727497$ and $172618865225769840779409899132552134222571512143$, respectively. The independent integer verifier also checks that these are all the sites with that value on each domain outside the supports. [Lean certificate](../../../ArkLib/Research/ProximityGap/Frontier/Order256LocatorCounterexamples.lean) · [Integer verifier](../../../scripts/probes/probe_mu256_locator_counterexamples.py)

## The complex separation

For the first two listed centers $a,b$, replace $z$ by an indeterminate $X$ and form the integer polynomial
\[
 F(X)=\prod_{j\in P}(X^a-X^j)\prod_{j\in Q}(X^b-X^j)
     -\prod_{j\in Q}(X^a-X^j)\prod_{j\in P}(X^b-X^j).
\]
If the ratios agreed at any complex primitive 256th root, its minimal polynomial $\Phi_{256}(X)=X^{128}+1$ would divide $F$ in $\mathbb Z[X]$. Since $3^{128}=-1$ modulo 257, this would give $F(3)=0$ in the auxiliary field. The two different auxiliary values in the table contradict this. Lean checks the integral minimal-polynomial divisibility and reduction in the same theorem. A separate verifier multiplies all binomials in $\mathbb Z[X]/(X^{128}+1)$ and finds the displayed nonzero constant terms. [Complex separation theorem](../../../ArkLib/Research/ProximityGap/Frontier/Order256LocatorCounterexamples.lean)

Both supports in each example are invariant under negation of the exponent. The paired factors $T^2-(z^j+z^{-j})T+1$ make their equal-degree quotient invariant under $T\mapsto T^{-1}$. This gives the two additional centers from the first comparison. The 58 and 60 changed odd sites show that finite-field constancy at four even centers also fails to force antipodal support symmetry on the opposite parity. Universal two-center transfer holds at order 128 and all its dyadic subgroups, so **256 is the first dyadic order where this implication from finite constancy to complex constancy fails for either named field**. [Order-128 transfer](mu128-unit-ellipsoid-transfer.md)

## The two production subgroups

Put $m=2^{22}$ and $n=256m=2^{30}$. In each field the certificate exhibits a generator $g$ of order $n$ with $g^m=z$. For either support, pulling it back under $T\mapsto T^m$ gives the monic locator
\[
 \prod_{j\in S}(T^m-z^j)=L_S(T^m).
\]
Each factor has the $m$ distinct roots $g^{j+256t}$ for $0\le t<m$, which accounts for its entire degree. The lifted supports remain disjoint and both have degree $62m=260046848<2^{28}-1$. All **$4m=16777216$ distinct test sites** in the four fibers have the common finite-field value. At any complex primitive $n$th root the first two fibers still give different ratios since its $m$th power is a primitive 256th root. Lean checks the full-order field generators, finite equalities on every lifted site, distinctness of all indices, the fiber zero-set formula and the corresponding complex separation. The order-256 odd-site asymmetry concerns the base examples; the production pullbacks consist of entire power-map fibers. [Production theorems](../../../ArkLib/Research/ProximityGap/Frontier/Order256LocatorCounterexamples.lean)

These examples disprove a uniform replacement of one named-field locator row by its characteristic-zero counterpart. The six simultaneous saturation rows and their signed face relation impose further conditions in the proximity-prize problem.

## Finding the examples

For a fixed pair of centers and inversion-invariant supports, assign a sign from $\{-1,0,1\}$ to each inverse pair of support sites. The signs sum to zero because the supports have equal size. Expand every paired ratio contribution as a power of $z$ times a monomial in the 64 primitive units $1-z^r$, $r=1,3,\ldots,127$. The verified full-field logarithms turn the finite equality into an integer congruence on the exponent vector and its phase. A Hermite basis incorporates the image of the integral source, the zero-sum condition and the phase modulus. Reduction of this lattice in the inverse covariance metric provided candidates. A bounded integer feasibility problem then recovered the signed inverse pairs. The proof of each final example requires only its literal cardinalities and polynomial evaluations.

The discrete logarithms came from index calculus with batch smoothness detection. Given a batch of rational-reconstruction numerators and denominators, a remainder tree evaluates one primorial modulo every candidate, allowing smoothness tests before full factorization. Every resulting logarithm was verified by exponentiation. [Bernstein, *How to find smooth parts of integers*](https://cr.yp.to/factorization/smoothparts-20040510.pdf)
