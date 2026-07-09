# Issue #466 R383: primitive-generator averaging

Date: 2026-07-09

## New route

R377 correctly refutes odd-exponent multiplier stability at one fixed generator. It does not
preclude averaging over every primitive generator of the same dyadic subgroup. The subgroup energy
is generator-independent. Swapping the generator and endpoint sums weights each endpoint by its
number of primitive-root zeros.

R383 proves the exact finite consumer

```text
card(generators) * commonKernelLoad
  <= maxPrimitiveRootMultiplicity * totalEndpointMass.
```

Unlike fixed-generator rotation compression, this compares distinct kernels and can yield a real
saving.

## Exact probe

`scripts/probes/probe_r383_primitive_generator_root_multiplicity.py` exhaustively enumerates
doubled-walk endpoints. The maximum number of primitive-generator roots was `1` in six tested
non-hostile cells:

```text
(n,p,r) = (8,17,2), (8,41,2), (8,73,3),
          (16,97,2), (16,113,2), (16,193,3).
```

The known hostile cell `(16,17,4)` reaches multiplicity `4`, so uniqueness is false without a
field-size/depth condition. The live arithmetic target is an effective multiplicity bound for
small-height endpoint polynomials over the primitive dyadic roots at prize scaling.

## Honest status

The double count is axiom-clean bookkeeping. It does not yet close CORE. The required multiplicity
bound is new proof debt; degree alone gives only the trivial `B < n/2`, while norm divisibility can
at best begin from the fact that `B` distinct split primes above `p` force `p^B` into the
cyclotomic norm.

More decisively, even the impossible dream input `B = 1` gives only a `1/phi(n) = 2/n` saving
against total doubled-walk mass. At the prize point `n = 2^30`, `r = 89`, this upper envelope has
base-2 logarithm `5311`, while the Wick fluctuation `(2r-1)!! * n^r` has base-2 logarithm about
`3207.44`: an overshoot of `2103.56` bits (about `10^633`). The DC scale needs the much larger
`1/q` normalization, with `q/n` approximately `n^3` beyond generator averaging.

Therefore generator averaging is not a standalone closure even under root uniqueness. To become
useful it must be composed with a genuinely centered cross-generator cancellation mechanism; a
better incidence cap alone cannot supply the missing `q/n` factor.
