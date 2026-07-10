# An unconditional field-dependent separation at rate `1/16`

Date: 2026-07-09
Campaign: #466
Status: end-to-end axiom-clean Lean proof; exact first-field pin and strict two-field separation

Companion files:

* `docs/kb/deltastar-466-half-predecessor-rate-sixteenth-2026-07-09.md`
* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_HalfPredecessorRateSixteenthFullWiring.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SeventeenThirtyTwoFullWiring.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeLowRateExactPins.lean`
* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30Second.lean`

## 1. Headline

For any distinct-domain Reed--Solomon code of rate at most `1/16`, the same rich-point
geometry that proves the exact half-predecessor count also gives a genuinely beyond-half
good point:

```text
epsMCA(RS, 17/32) <= 2n / |F|.                    (1)
```

This is field-size-free as a bad-scalar count.  It uses no Johnson-package residual, no
character sum, and no multiplicative-subgroup property.

Consequently, for `Q=2^128`, `n=2^30`, and the certified prime

```text
P2 = 730750818665451459101842416358141509841924915201
   = 0x8000000000000000000000000000000340000001,
```

we have

```text
floor(P2/Q)=2n,       P2 = 1 (mod n),
```

and hence a smooth order-`n` RS code over `F_P2` satisfies

```text
mcaDeltaStar(RS,1/Q) >= 17/32 > 1/2.              (2)
```

By contrast, the companion half-predecessor theorem plus the overlap packing pins
`mcaDeltaStar=1/2` on the certified prime branch with `floor(P1/Q)=n`.  Thus the operational
threshold is provably field-dependent: the rate, length, smoothness order, and error budget alone
do not determine one number.  This refutes any **rate-only** answer to the prize question.  It does
not by itself resolve the full Grand MCA challenge as presently worded: that challenge writes the
answer as `deltaStar_C`, permits dependence on the particular code, and asks about all four prize
rates.  The result here exactly determines one concrete prize-parameter code and separates it from
a second; the second code currently has a strict lower pin, not a matching exact upper pin.

`_PrizeShapePrimeP30Second.lean` kernel-certifies that `P2` is prime, that
`P2/2^128=2^31`, and that the explicit element

```text
192152681249815148642741928588691886362054863855
```

has exact order `2^30`.  Its axiom audit contains only the standard
`propext`, `Classical.choice`, and `Quot.sound`; none of the coding-theory proof below depends on
this particular integer.

## 2. Setup

Write

```text
n=2h,        16 | h,        t=15h/16,        d=k-1,
16k<=n.
```

The rate inequality is

```text
8d+8 <= h.                                          (R)
```

The radius associated to agreement `t` is

```text
delta = 1 - t/n = 1 - 15/32 = 17/32.
```

As in the companion proof, choose one degree-`<k` polynomial for each bad scalar and take
its full agreement set.  This gives distinct lifted points

```text
P_gamma=(gamma, coeff(q_gamma)) in F^(k+1)
```

and `2h` affine hyperplanes, with every selected point incident to at least `t` hyperplanes.
For an affine line `ell` of selected points, let `z_ell` be its joint-core size and `L_ell`
its number of selected points.  The exact fresh-fiber law remains

```text
L_ell * max(1,t-z_ell) + z_ell <= 2h.              (L)
```

An off-line point meets the core in at most `d` coordinates, and a noncollinear triple has
common codegree at most `d`.  These statements are proved in full in the companion note and
hold over every field characteristic.

## 3. General line bound and the high-core branch

From `(L)`, every selected line has

```text
L_ell <= 2h-t+1 = 17h/16+1.                        (G)
```

Indeed, if `z<t`, divide `(L)` by `t-z` and use

```text
(2h-z)/(t-z) = 1 + (2h-t)/(t-z) <= 2h-t+1;
```

if `z>=t`, the mandatory one fresh coordinate gives `L<=2h-z<=2h-t`.

Suppose there were more than `4h=2n` bad scalars.  Restrict to exactly

```text
N=4h+1                                                (N0)
```

selected points.  All incidence and nonjoint properties are inherited.

Fix a selected line with core `D`, `|D|=z`.  Every outside agreement set contains at least
`t-d` coordinates in `D^c`.  Three outside points therefore share at least

```text
3(t-d)-2(2h-z)
```

coordinates outside `D`.  If

```text
2z > 4h-3t+4d = 19h/16+4d,                         (H)
```

this is greater than `d`, so every outside triple is collinear.  There are at least three
outside points: by `(G)` and `(N0)`, their number is much larger than `h`.  Hence all outside
points lie on one affine line.  The whole set lies on two lines and `(G)` gives

```text
N <= 2(17h/16+1)=17h/8+2 < 4h+1,
```

a contradiction.

Thus every line in a hypothetical counterexample obeys the low-core cap

```text
2z <= 19h/16+4d.                                    (Hc)
```

## 4. Every surviving line has at most twelve points

Put `h=16m`, so `t=15m` and the block length is `32m`.  The cap is

```text
2z <= 19m+4d.
```

Together with `(R)`, this puts `z<t`.  If `L>=13`, the left side of `(L)` is at least

```text
13(15m-z)+z = 195m-12z.
```

Multiplying the core cap by six and the rate inequality by three gives

```text
12z <= 114m+24d <= 162m-24.
```

Therefore

```text
195m-12z >= 33m+24 > 32m,
```

contradicting `(L)`.  Hence

```text
L_ell <= 12.                                         (S)
```

This exact natural-number calculation is consumed by the axiom-clean end-to-end assembly
`SeventeenThirtyTwoFullWiring.badScalarRichPointFamily_card_le_sixtyFour_mul`.

The core excess over the noncollinear codegree satisfies

```text
z-d <= 23h/32-1.                                     (C)
```

To see it, subtract `2d` from `(Hc)` and use `2d+2<=h/4`, which follows from `(R)`.

## 5. Third-moment contradiction

Let `m_i` be the number of selected points incident to coordinate hyperplane `i`, and set

```text
T=sum_i C(m_i,3).
```

The total incidence is at least `Nt`, so discrete convexity gives the balanced lower bound.
At `(N0)`, the average incidence is

```text
a = Nt/(2h) = 15N/32.
```

Thus six times the lower bound is

```text
lowerSix = 2h*a(a-1)(a-2).                           (LB)
```

For the upper bound, every noncollinear triple contributes at most `d`.  Collinear triples
receive the excess `(C)`.  Since a line has at most twelve selected points,

```text
C(L,3) = (L-2)/3 C(L,2) <= 10/3 C(L,2).
```

Every pair determines a unique affine line, so the number of collinear triples is at most
`(10/3)C(N,2)`.  Six times the upper bound is therefore

```text
upperSix = (h/8-1)N(N-1)(N-2)
           +10(23h/32-1)N(N-1).                     (UB)
```

At `N=4h+1`, direct expansion has a positive-coefficient form around the smallest allowed
`h=16`.  If `x=h-16>=0`, then

```text
1024*(lowerSix-upperSix)
  = 121943055
    +(678102863/16)x
    +(20919437/4)x^2
    +276013x^3
    +5308x^4
  > 0.                                               (P)
```

This contradicts `LB <= 6T <= UB`.  Hence the number of bad scalars is at most `4h=2n`,
proving `(1)`.

The identity `(P)`, its positivity, and the abstract third-moment contradiction are checked
axiom-clean in Lean and wired to the literal MCA filter by:

```text
seventeenThirtyTwo_endpoint_expansion
upperSixSeventeenThirtyTwo_lt_lower
no_thirdMoment_bounds_at_seventeenThirtyTwo
SeventeenThirtyTwoFullWiring.seventeenThirtyTwo_badScalar_filter_card_le_two_mul_length
```

The final smooth-domain specializations are:

```text
PrizeShapeLowRateExactPins.firstPrime_rateSixteenth_deltaStar_eq_half
PrizeShapeLowRateExactPins.secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar
PrizeShapeLowRateExactPins.secondPrime_rateSixteenth_half_lt_deltaStar
```

Running `scripts/pg-iterate.sh` on `_PrizeShapeLowRateExactPins.lean` checks this entire bridge,
including the concrete `evalCode`/Reed--Solomon identification, with no `sorryAx`; the audit uses
only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## 6. The concrete `P2` arithmetic

Let

```text
Q=2^128, n=2^30,
P2 = (2n)Q + 13n + 1.
```

Then `13n+1<Q`, so

```text
floor(P2/Q)=2n.
```

Also `n | P2-1`, so the multiplicative group of the prime field contains an element of
order `n` by cyclicity.  The decimal and hexadecimal forms are

```text
P2 = 730750818665451459101842416358141509841924915201
   = 0x8000000000000000000000000000000340000001.
```

OpenSSL independently reports:

```text
8000000000000000000000000000000340000001 (...) is prime
```

Applying `(1)` gives

```text
epsMCA(RS,17/32) <= 2n/P2 <= 1/Q,
```

and the threshold ledger yields `(2)`.

## 7. Stronger shallow-rung expectation

The same dichotomy appears to prove the exact packing envelope for a short interval above
`1/2`.  At agreement `t=h-r`, the packing count is

```text
2(2h-t)+2 = 2h+2r+2.
```

The high-core branch always gives a union of two lines, each of size at most `2h-t+1`,
which is exactly this count.  For fixed `r` (and experimentally for `r` up to about `h/10` at
rate `1/16`), the low-core third moment still rules out the next scalar.  In particular, the
calculations for `r=0,1` support the sharp bounds `n+2` and `n+4`.  Formalizing those two rungs
would pin a second exact field branch (`floor(p/Q) in {n+2,n+3}` gives
`delta*=1/2+1/n`), but this note claims only the fully audited `2n` bound at `17/32` and the
half-predecessor theorem from its companion.
