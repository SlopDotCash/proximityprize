# Issue #466 R397: diagonal Lucas/subresultant obstruction (REFUTED threshold)

## Verdict

The Lucas reduction is correct and Lean-verified, but the proposed `p<n^4` prime-factor bound is
**false**. At `n=128`, the degree-one subresultant content has the prime factor

```text
p = 9430378268417 = 1 (mod 128) > 128^4 = 268435456.
```

This is not a leading-coefficient artifact. Taking `3` as a primitive root modulo `p` and
`z=3^((p-1)/128)`, direct evaluation gives the ordered solutions

```text
(0,0), (5,87), (87,5), (23,110), (110,23).
```

Thus the three distinct unordered supports are `{0,0}`, `{5,87}`, and `{23,110}`. Pair
multiplicity is `5`, so R394's original hypothesis `PairMultiplicityFour` fails beyond the quartic
threshold. The proposed R397 arithmetic theorem is retired. R393 was subsequently sharpened from
24 to 12 canonical permutations, so the corrected R394 consumer needs only `PairMultiplicityEight`;
the finite `105n` route itself survives this counterexample.

## Exact reduction

Suppose one of three pair supports is diagonal.  Scale its nonzero common sum so that this support
is `(1,1)`.  Every other support is then `{x,y}` with

```text
x + y = 2,     x^n = y^n = 1.
```

For `s=xy`, define

```text
P_0(s)=2,  P_1(s)=2,  P_{k+2}(s)=2P_{k+1}(s)-sP_k(s).
```

Then `P_k(s)=x^k+y^k`; hence every extra support gives

```text
s^n = 1,       P_n(s) = 2.
```

Different unordered supports have different products, since sum and product determine their
quadratic. Thus two supports beyond `{1,1}` force the gcd of `X^n-1` and `P_n(X)-2` over `F_p`
to have degree at least three, including the baseline product `s=1`; after deflating that baseline,
the gcd has degree at least two. `_R397DiagonalPairLucasReduction.lean` formalizes the recurrence,
the forward common-root implication, and product injectivity on fixed-sum supports.

Equivalently, writing `x=1+t`, `y=1-t`, the two root equations split into the even and odd
binomial polynomials in `u=t^2`.  If `C(u)` and `D(u)` denote their even and odd parts, the exact
identity

```text
C(u)^2 - u D(u)^2 = (1-u)^n
```

comes from `(1+t)^n(1-t)^n=(1-t^2)^n`.

## Degree-one subresultant experiment

For dyadic `n`, gcd degree at least two forces the degree-one subresultant to vanish identically
modulo `p`; therefore `p` divides its integer content.  Exact SymPy computations give the following
admissible prime factors (`p = 1 mod n`) of that content:

```text
n=16: 17, 113
n=32: 97, 193, 257, 32993
n=64: 193, 257, 449, 577, 641, 769, 1409, 3457,
      5569, 7937, 65537, 11127041
```

Every listed prime through `n=64` is strictly below `n^4`. In particular, the previously largest observed
diagonal obstruction `p=11127041` appears automatically in the `n=64` content. This initially
suggested the arithmetic theorem:

> For dyadic `n`, every prime `p = 1 mod n` dividing the degree-one subresultant content of
> `X^n-1` and `P_n(X)-2` satisfies `p < n^4`.

This is a prime-selective statement.  It does **not** assert that the content, resultant, Smith
index, or largest invariant factor is below `n^4`; those stronger size claims are false.

The `n=128` counterexample above refutes this statement.

## Surviving content

The exact Lucas reduction and the fact that distinct fixed-sum supports have distinct products
remain useful structural facts. They no longer support a uniform multiplicity-four cap. Any
R393's antipodal-cover accounting has now been sharpened enough to tolerate every fiber of size at
most eight. The live arithmetic questions are therefore `PairMultiplicityEight` and
`PrimitiveFourBoundNine`, rather than the refuted multiplicity-four statement.

## Second refutation: multiplicity eight also fails

At `n=256`, the degree-three subresultant content has the admissible prime factor

```text
p = 67280421310721 = 1 (mod 256) > 256^4 = 4294967296.
```

With `z=3^((p-1)/256)`, the equation `z^i+z^j=2` has nine ordered solutions and five supports:

```text
(0,0), (6,9), (67,131), (70,140), (73,134)
```

(with both orders for each non-diagonal support). Hence `rep2(2)=9>8`; `PairMultiplicityEight` is
not universal either. Importantly, direct convolution gives

```text
rep4(1)=rep4(2)=24865 < 105*256 = 26880.
```

So the pair cap is the wrong surrogate: it fails while the desired nonzero four-fiber bound survives
this stress test. The live finite target is now the direct `rep4(c)<=105n` theorem, not another
constant pointwise bound on `rep2`.
