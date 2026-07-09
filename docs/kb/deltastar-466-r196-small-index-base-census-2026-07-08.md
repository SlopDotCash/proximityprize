# δ* #466 — small-index base census for the spike route (2026-07-08)

## Hypothesis

R194 suggested splitting the spike-mass proof into:

1. a finite tiny-index base range;
2. a large-index logarithmic max estimate.

R196 exhausts dyadic cases with

```text
M = (p - 1) / n < 32
p = M n + 1 prime
n = 2^a
```

through `a = 12`.

## Probe

File: `scripts/probes/probe_r196_small_index_base_census.py`.

For every small-index prime, it computes exact:

```text
MGF(1/4)
R189 weighted budget
exp(max(X)/4) / M
```

## Result

```text
tested = 75
spike-ratio target = 0.199786
violations_target = 38
worst_ratio = 0.719919 at n=8, p=17, M=2
worst_budget = 2.094093
worst direct MGF(1/4) = 1.5031
```

Interpretation:

- The crude R191/R194 spike-ratio target is not intended for tiny `M`.
- Some tiny cases also exceed the R189 envelope budget `2`.
- Direct quarter-MGF is still safely below `2` across the entire finite census.

Representative worst rows:

```text
ratio     budget   mgf1/4  maxX    M    n      p
0.719919  1.3389   1.2925  1.458   2    8      17
0.662272  1.3389   1.2846  1.124   2    128    257
0.557960  1.6230   1.3099  2.061   3    64     193
0.436469  2.0380   1.4172  5.002   8    32     257
0.426995  2.0911   1.4570  6.188   11   128    1409
0.341524  2.0941   1.5031  8.735   26   512    13313
```

## Verdict

The proof path should split as:

1. `M < 32`: finite direct `DyadicQuarterMGFBound` certificates;
2. `M ≥ 32`: R189/R190 bulk-plus-two envelope plus R194 logarithmic max bound.

This avoids forcing the large-index spike-ratio proof to cover tiny degenerate
coset counts where the envelope is too coarse but the actual MGF bound is easy.
