# δ* #466 — child-threshold implication audit (2026-07-08)

## Hypothesis

R188 found that the very top dyadic spikes are same-sign merges of two already
large child periods.  A tempting strengthening is:

```text
X_parent ≥ T  =>  min(X_child0, X_child1) ≥ cT
```

for a fixed positive `c`.  R189 tests this over the whole high tail.

Probe: `scripts/probes/probe_r189_child_threshold_implication.py`.

## Result

```text
n 64 p 16778497
T 4 N 11712 min-child fraction all>= 0
T 6 N 3515 min-child fraction all>= 0
T 8 N 1064 min-child fraction all>= 0
T 10 N 355 min-child fraction all>= 0
T 12 N 118 min-child fraction all>= 0
T 16 N 22 min-child fraction all>= 0.25
T 20 N 2 min-child fraction all>= 0.4

n 128 p 268437889
T 4 N 95115 min-child fraction all>= 0
T 6 N 29386 min-child fraction all>= 0
T 8 N 9352 min-child fraction all>= 0
T 10 N 3000 min-child fraction all>= 0
T 12 N 954 min-child fraction all>= 0
T 16 N 108 min-child fraction all>= 0.1
T 20 N 14 min-child fraction all>= 0.25

n 256 p 16777729
T 4 N 2934 min-child fraction all>= 0
T 6 N 934 min-child fraction all>= 0
T 8 N 311 min-child fraction all>= 0
T 10 N 92 min-child fraction all>= 0
T 12 N 28 min-child fraction all>= 0
T 16 N 2 min-child fraction all>= 0.33
```

## Verdict

The naive two-large-children implication is false for the moderate high tail.
Many `X_parent ≥ 4..12` events can be produced by one large child plus one
small child.  The two-large-child ancestry observed in R188 is an
**extreme-tail** phenomenon, not a full-tail theorem.

Corrected proof target:

```text
Split parent tails into:
1. one-big-child events, controlled by the child tail recursively;
2. two-large-same-sign events, controlled by child-pair angle/mixed
   equidistribution.
```

This is the right recursive shape for a no-far-spike theorem.  It mirrors the
elementary inequality

```text
(a+b)^2 ≥ T  =>  (a^2 large) OR (b^2 large) OR (same-sign balanced merge).
```

Honest scope: R188's simple ancestry story was too strong.  R189 corrects it
to a two-channel recursion: inherited single-child spikes plus genuinely new
aligned-pair spikes.
