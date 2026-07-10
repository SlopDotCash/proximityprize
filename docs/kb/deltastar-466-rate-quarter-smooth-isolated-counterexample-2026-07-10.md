# Delta-star rate quarter: smooth isolated-fibre counterexample (2026-07-10)

## Status

An exact certificate refutes the hoped-for half-predecessor `n`-scalar bound
at rate `1/4`, first over the genuine `mu_32` domain in `F_97`, and then by an
arithmetic scale lift at the certified prize prime `P1` and its
`mu_(2^30)` domain.  The finite `F_97` certificate is now kernel-checked in
`Frontier/_HalfPredecessorRateQuarterSmoothCounterexampleF97.lean`: at radius
`15/32`, dimension eight, its literal MCA bad-scalar filter has at least 36
members, hence strictly more than the domain size 32.

At the prize parameters

```text
m = 2^26,
n = 16m = 2^30,
k = 4m = 2^28,
agreement threshold = 2k+1,
```

the construction has

```text
15m safe bad scalars + 3m isolated bad scalars
  = 18m = (9/8)n = 1,207,959,552 > n.
```

The same fibre assignment can be thickened until only one hole coordinate
remains.  It then has `n+2` bad scalars at radius
`23/48-1/(24m)`, about `0.4791667`.  In particular, the rate-quarter
operational threshold is strictly below `1/2`; the unconditional exact-half
strategy that succeeds at rates `1/8` and `1/16` cannot extend to rate `1/4`.

The prize-scale pointwise/coset proof is now fully transcribed into Lean.
`_P1RateQuarterScaleConstruction.lean` builds the billion-coordinate smooth
domain and stack parametrically, `_P1RateQuarterScaleBadCount.lean` proves the
literal `N+2` event count, and `_P1RateQuarterScaleFinalConsumer.lean` proves
the operational `mcaDeltaStar` upper bound at error `2^-128`.  All three use
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## The universal `mu_16` locator identity

Let `zeta` be a primitive sixteenth root, and take the disjoint exponent
triples

```text
A = {0,1,8},
B = {2,9,10},
C = {3,5,7}.
```

Write `p_A,p_B,p_C` for their monic cubic locators.  Directly from
`zeta^8=-1`,

```text
p_C = (1-lambda) p_A + lambda p_B,
lambda = (1-zeta^2-zeta^4-zeta^6)/2.
```

The identity was exhaustively rediscovered over `F_97` (one of 160 disjoint
collinear locator triples), reproduced over `F_113` and `F_193`, and then
checked exactly at `P1`.  Its proof is cyclotomic, not field-specific.

## Smooth scale lift

Let `g` have order `n=16m`, set `zeta=g^m`, and use the fibre map

```text
x |-> x^m : mu_n -> mu_16.
```

Each exponent in `mu_16` has a fibre of size `m`.  Lift the three root triples;
their inverse images `E12,E23,E13` are pairwise disjoint and have size `3m`.
Use two of the seven remaining fibres as a private block for each of three
lines, leaving the last fibre `H0` uncovered.  Thus

```text
D1 = E12 union E13 union U1,
D2 = E12 union E23 union U2,
D3 = E13 union E23 union U3,
|Di| = 3m+3m+2m = 8m = 2k,
|D1 union D2 union D3| = 15m,
|H0| = m.
```

Define

```text
f1 = 0,
f2 = (1-lambda) p_A(X^m),
f3 = p_C(X^m).
```

Then the three differences vanish on the intended pair cores.  Use primitive
direction `(X,1)` and polynomial-line pairs

```text
c_i = (X f_i, f_i).
```

Their component degrees are at most `3m+1 < 4m=k`.  On each core `D_i`, set
the received pair equal to `c_i`.

## The `15m` covered-fibre witnesses

Every covered coordinate `x` lies outside at least one core `D_i`.  On any
such source line take

```text
gamma = -x,
q_(i,x)(X) = f_i(X) (X-x).
```

The polynomial agrees with the received affine word on `D_i union {x}`, which
has `2k+1` coordinates.  It has degree `<k`.  Joint explanation is impossible:
the `2k` core coordinates uniquely force the two explaining degree-`<k`
polynomials to be `(X f_i,f_i)`, and that pair fails at the fresh coordinate
`x`.  Distinct covered coordinates give distinct `gamma=-x`, hence `15m`
nonjoint bad scalars.

## The `3m` isolated-fibre witnesses

On the uncovered fibre choose a received pair

```text
(u0(x),u1(x)) = (alpha*x,beta).
```

Each `f_i` is constant there; write its value `t_i`.  If `beta != t_i`, then

```text
c_i = (t_i-alpha)/(beta-t_i),
gamma_(i,x) = c_i*x
```

satisfies

```text
alpha*x + gamma_(i,x)*beta = t_i*(x+gamma_(i,x)).
```

Therefore `f_i(X)(X+gamma_(i,x))` has the same `2k+1`-coordinate nonjoint
witness `D_i union {x}`.  Choose `alpha,beta` so that each multiplicative coset
`c_i H0` is outside `mu_n` and the three cosets are distinct.  This gives `3m`
new scalars, disjoint from the `15m` safe scalars inside `mu_n`.

At `P1`, the tiny choice

```text
alpha = 1,
beta = 2
```

works.  The exact constants are recorded by the probe, together with the
certificates

```text
c_i^n != 1,
(c_i/c_j)^m != 1  for i != j.
```

These are precisely the two conditions needed for the unsafe cosets to lie
outside `mu_n` and to be pairwise disjoint.

## Maximal thickening and the sharper prize upper certificate

The half-predecessor presentation is not the strongest radius carried by the
same construction.  Here `m=2^26` satisfies `m=1 (mod 3)`.  Partition all but
one coordinate of the old hole fibre into three disjoint sets of size

```text
r = (m-1)/3
```

and add one set to each decoded-line core.  A moved coordinate owned by line
`j` remains a safe fresh coordinate for either other source line at
`gamma=-x`; the three distinct hole-fibre values `t_i` give the required
cross-line mismatch.  One residual hole coordinate retains the three
isolated bad labels.  The exact ledger becomes

```text
core size              = 8m + r,
agreement threshold    = 8m + r + 1 = (25m+2)/3,
safe bad scalars       = n-1,
isolated bad scalars   = 3,
total bad scalars      = n+2 > n.
```

Thus the certified bad radius is

```text
delta_upper = (n-(8m+r+1))/n
            = (23m-2)/(48m)
            = 23/48 - 1/(24m).
```

At `m=2^26` this is strictly below `23/48`, about `0.4791667`, rather than
merely the last lattice point below `1/2`.  The construction cannot thicken
all three cores further by this disjoint assignment while retaining an old
hole coordinate; filling the final hole drops the displayed scalar count to
`n`.  This is maximality of this particular fibre assignment, not a proof
that no different construction becomes bad at a smaller radius.

## Executable certificates

* `scripts/probes/probe_rate_quarter_primitive_isolated_counterexample.py`
  gives the first arbitrary-domain example: `F_101`, `(n,k)=(28,7)`, with
  `30>28` bad scalars.
* `scripts/probes/probe_rate_quarter_smooth_split_locators.py` exhausts the
  `mu_16` cubic-locator cell and checks the universal triple at several primes.
* `scripts/probes/probe_rate_quarter_smooth_isolated_counterexample.py` gives
  the full `F_97`, `mu_32`, `[32,8]` witness with `36>32` bad scalars.
* `scripts/probes/probe_rate_quarter_prize_p1_isolated_counterexample.py`
  checks the locator identity, degree ledger, fibre counts, pointwise hole
  equations, and unsafe-coset separation at the actual `P1` modulus.

## Operational consequence and next target

At the certified P1 prime, the exact prize budget is crossed by the displayed
`N+2` events.  The half-predecessor stack has `(9/8)n`; the
maximally thickened stack still has `n+2`.  The executable operational upper
certificate is therefore the sharper radius

```text
(23m-2)/(48m) = 23/48 - 1/(24m).
```

This falsifies the exact-half hypothesis and substantially lowers its upper
bracket, but it does not determine rate-quarter `deltaStar`.  A subsequent
degree-saturated common-factor amplifier gives the stronger executable radius
`43/96+1/(3n)`; its full operational assembly is tracked separately.  An exact
pin still requires a matching uniform lower bound or a still smaller bad
construction.
