# R318 Rational Resonance at Deep Moment Depth

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R317 proposes separating the shadow collision mass into nonresonant components
and rational-resonance webs.  R307--R316 show that the `3 in mu_n` web really
violates the exact depth-3 Wick constant.  Does that obstruction grow too fast
to fit the prize-facing allowance `K^r * (2r-1)!! * n^r`?

## Complete coset computation

`probe_r318_resonance_deep_moments.py` evaluates every Gauss period for

```text
n = 32, p = 21523361, [F_p^x : mu_n] = 672605,
```

the unique high-beta exact-Wick violator in the complete R305 census.  Because
`eta_b` is constant on multiplicative cosets, this requires only 672605 period
evaluations.  For each depth it reports `K_eff` defined by

```text
sum_(b != 0) |eta_b|^(2r)
  = p * K_eff^r * (2r-1)!! * n^r.
```

The result is unexpectedly favorable:

```text
r=3   K_eff=1.0092
r=5   K_eff=1.0137
r=8   K_eff=1.0105
r=16  K_eff=0.9344
r=32  K_eff=0.7008
```

The exact Wick constant fails at shallow depth, but the exponential loss is
tiny and turns downward before `r = log p`.  The known `c=3` obstruction is
therefore compatible with the prize-facing deep-moment form.

## Checks

At `r=1`, the computed ratio is `1 - n/p` to floating precision, matching the
exact nonzero-frequency Parseval identity.  At `r=3`, it matches the R308 energy
`E_3 = (15n^3 - 45n^2 + 40n) + (60n^2 - 90n)` after DC subtraction.

## Interpretation

This rejects a plausible refutation of R317: rational resonance does not by
itself force an unbounded `K_eff`.  A possible winning theorem now has the form

```text
heavy collision component
  => small rational stabilizer
  => resonance transfer matrix with spectral cost <= K^r.
```

The computation does not prove either implication, and the small `n=32` cell
cannot determine uniformity in `n`.  It does show that the worst currently
known fixed-depth counterexample behaves correctly at logarithmic depth, which
is the depth the prize actually consumes.

## Status

Exact full-coset numerical evidence, not a theorem.  No prize closure claimed.
