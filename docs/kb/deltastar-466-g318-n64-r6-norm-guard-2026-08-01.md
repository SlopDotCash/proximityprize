# G318: norm guard certifies the `n=64`, rank-6 antipodal count

Date: 2026-08-01
Issue: #466
Branch: `research/proximity-prize`

## Result

G317 checked `n=64,r=5` directly. The `n=64,r=6` sparse histogram is expected to need about
`58,573,633` support states, so G318 uses a cyclotomic norm guard instead of a huge dictionary.

Let `zeta` be a primitive 64th root. Any relation counted by the coefficient-`a` adjacent-rank dot
has the shape

```text
zeta^u + sum_{i in A} zeta^i - sum_{j in B} zeta^j - a = 0 mod p,
```

with `|A|=6`, `|B|=5`, and `a in {1,2}`. Its coefficient `l1` norm is at most `14`. If the
corresponding cyclotomic integer is nonzero, its algebraic norm has absolute value at most

```text
14^phi(64) = 14^32.
```

The certified Proth prime

```text
p = 111*2^128 + 1
```

satisfies `p > 14^32`. Therefore a nonzero relation cannot vanish modulo `p`: if it did, `p` would
divide its nonzero algebraic norm, whose absolute value is smaller than `p`. Hence every finite-field
relation in the `n=64,r=6` coefficient-1/2 audit is already a complex cyclotomic relation. For 64th
roots, those are exactly the antipodal-pair cancellations.

Combining this guard with the G316 formula gives the exact rank-six finite-field constants:

```text
coefficient 1: dot=0,           A=-2341449599010471936
coefficient 2: dot=20331698688, A=+767955559391433686463300268059000302726608177666560
```

## Scope

This is a finite `n=64,r=6` certificate, not a production theorem. The norm guard works here because
`14^32 < p`; at larger orders, the cyclotomic degree grows and this simple inequality no longer
reaches the production regime. The useful content is that the rank-six `n=64` field count is
certified without materializing the huge histogram.

## Artifact

- Probe: `scripts/probes/g318_n64_r6_norm_guard.py`
- Output: platform temp directory `arklib-reports/g318_n64_r6_norm_guard.out`
