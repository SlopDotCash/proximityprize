# δ* #466 — large-n stress test for normalized moment-ratio monotonicity (2026-07-08)

## Hypothesis

R58 proposed a closing-grade theorem shape:

```text
R_{r+1}(μ_n) ≤ R_r(μ_n),
R_r = Σ_{b≠0}|η_b|^(2r) / ((p-1)(2r-1)!!σ^(2r)).
```

If true uniformly, low-rung sub-Wick bounds propagate to the deep moment depth used by the prize.

R59 stress-tests this candidate at larger `n` and deeper `r`, using the fact that `|η_b|` is
constant on `μ_n`-cosets, so one representative per coset suffices.

Probe: `scripts/probes/probe_r59_large_moment_ratio_monotonicity.py`.

## Result

Exact coset-spectrum computations:

```text
n=64  p=16777601   cosets=262150  max_r=24  monotone=True
  R1=1.000000 R2=0.984301 R3=0.952745 R4=0.907725 R5=0.854545
  R20=0.0273226 R21=0.0152043 R22=0.00808874 R23=0.00412077 R24=0.00201347

n=128 p=268437889  cosets=2097171 max_r=16  monotone=True
  R1=1.000000 R2=0.992168 R3=0.976206 R4=0.952901 R5=0.923909
  R12=0.476241 R13=0.377237 R14=0.284802 R15=0.204747 R16=0.140165
```

No monotonicity failures appeared.

## Verdict

The normalized moment-ratio monotonicity hypothesis is still alive and stronger after this stress
test.  The decay is not merely local near `r=1`: for `n=64`, it persists through `r=24`, and for
`n=128` through `r=16`.

This is now one of the cleanest proof targets exposed by the exploration cycle:

```text
prove R_{r+1}(μ_n) ≤ R_r(μ_n)
```

or find the first counterexample.  Generic positive-measure arguments cannot prove it (R20 gives
ordinary log-convexity in the opposite direction, and R58 random symmetric controls violate this
normalized monotonicity).  Any proof must use the multiplicative/cyclotomic structure of `μ_n`.
