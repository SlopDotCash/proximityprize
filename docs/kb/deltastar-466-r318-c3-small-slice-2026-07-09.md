# #466 R318 — a seven-exception `c = 3` small-fiber slice

## New parameterization

Let `n = 2m`, choose an oriented primitive root `ζ` with

```text
ζ^h = 3,     k = m - h,
```

so `3ζ^k = -1`.  R317 now proves, for every `s,t`,

```text
ζ^s + ζ^(s+t) + ζ^(s+k)
  = ζ^(s+t) - 2ζ^(s+k).
```

This is a raw two-parameter collision family.  The newly observed candidate
small-fiber slice removes exactly

```text
{0, k, m, m+k, h+1, m+h, m+h+1}  (mod n).
```

For every remaining `(s,t)`, the two char-zero shadows are predicted to have
weights `(6,3)`, and their common field values are predicted to be distinct.
That would give precisely `n(n-7)` small fibers directly, without quotienting
the R316 H/K/D template catalogue.

## Exact evidence

`scripts/probes/probe_r318_c3_large_small_parametrization.py` checks all
parameter pairs and every char-zero shadow count, not a sample.  It passes on
the three known high-beta `c = 3` instances:

```text
n=32:  800   = 32(32-7)  distinct centers
n=64:  3648  = 64(64-7)  distinct centers
n=128: 15488 = 128(128-7) distinct centers
```

Each checked pair has exact shadow signature `(6,3)`, evaluates equally, and
has a distinct center.  The probe automatically selects a signed primitive
root orientation; at `n=32` it finds a different but equivalent orientation
than the earlier hand-selected one.

## Lean bridge and arithmetic endpoint

- `Frontier/_R317C3LargeFiberConstruction.lean` proves the complementary
  `3ζ^k=-1`, large-fiber, small-fiber, translated-small-fiber, and
  distinct-large-center field identities.
- `Frontier/_R318C3LargeSmallMass.lean` proves that `n` large fibers of mass
  `24n-18` plus `n(n-7)` small fibers of mass `36` already exceed the exact
  depth-3 Wick headroom for every `n >= 16`:

```text
large + small - headroom = 5n(3n-46) > 0.
```

- `Frontier/_R319C3SmallCenterCollisionReduction.lean` proves that equality
  of two raw small centers is *equivalent* to one explicit four-term relation.
- `Frontier/_R320C3SmallCenterResultant.lean` encodes that relation as the
  six-slot pattern `ζ^a + 2ζ^d = ζ^b + 2ζ^c` and uses FS3 to give every
  nonzero reduced pattern a bounded cyclotomic resultant divisible by every
  characteristic realizing the collision.

Thus the middle `(6,3,3)` stratum is no longer needed to force an exact-Wick
failure; the remaining proof task is only the finite-combinatorial realization
and injectivity of the large and seven-exception small slices.

## Refutation pass: the visible guards are insufficient

The slice is **not yet a theorem under just `ζ^h=3`**, even after demanding
seven distinct exclusions and enough field elements.  At `n=16`, `p=193`,
choose the primitive orientation `ζ=3`, `h=1`, `k=7`.  All 144 retained
parameter pairs have local signature `(6,3)`, but they collapse to only 128
centers.  One explicit collision is

```text
(s,t) = (0,6) and (13,13),
ζ^6 - ζ^10 - 2ζ^7 + 2ζ^4 = 0  (mod 193).
```

Indeed this evaluates to `-62532 = -193 * 324`.  So a proof needs a genuine
four-term center-collision exclusion (equivalently, control of the relevant
small resultant divisors), not merely the single `c=3` relation plus local
shadow multiplicities.

The even smaller `n=16, p=17` case fails by cardinality (`17 < 16·9`), while
the `n=8, p=41` instance happens to pass.  These checks are included to keep
the high-beta pattern an honest conjectural target rather than a claimed law.

## Status

This is a real reduction of the R315/R316 classification problem, not a prize
closure.  It isolates a concrete new residual:

```text
C3SmallCenterInjective:
  the seven-exception raw parameter map has no four-term center collisions.
```

At fixed `n` it is a finite resultant-divisor condition; R320 now formalizes
the per-pattern prime-divisor certificate.  Uniform counting/control at prize
scale remains open and is part of the same arithmetic collision wall.
