# #466 R309 — Lean socket for the `c=3` relation-web excess formula

## What R308 exposed

R308 found that the dangerous `c = 3` binomial norm relation-web at `n = 64` and `n = 128`
has exactly three positive collision-delta strata:

```text
count n        at delta 24n - 18
count 2n       at delta 90
count n(n-7)   at delta 36
```

This was observed in:

```text
scripts/probes/_out_466_r308_n64_c3_danger.txt
scripts/probes/_out_466_r308_n128_c3_danger.txt
```

## Lean result

New file:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R309C3RelationWebFormula.lean
```

It proves the algebraic consequence of that histogram:

```text
n(24n - 18) + 2n*90 + n(n-7)*36 = 60n² - 90n
```

and verifies that this beats the exact-Wick depth-3 headroom:

```text
60n² - 90n > 45n² - 40n   for every n >= 4.
```

Equivalently, the excess over headroom is:

```text
5n(3n - 10).
```

Validation:

```bash
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R309C3RelationWebFormula.lean
```

passed in 30s, axiom-clean (`propext`, `Classical.choice`/`Quot.sound` audit only; no `sorryAx`).

## Attempted next-rung stress

Factoring `3^128 + 1` for `n = 256` found several prime factors `p ≡ 1 (mod 256)`, including
beta `8.382`.  A brute-force `build_n3(256)` evaluation was started but stopped: the pure
Python triple enumeration is too slow for useful iteration at this rung.  No `n = 256`
classification claim is made here.

## Status

This does not prove the relation-web classification.  It proves the arithmetic endgame:
if the R308 three-stratum `c=3` histogram holds at a dyadic `n`, then exact-Wick depth 3
fails automatically.

The remaining theorem-shaped target is:

```text
C3RelationWebHistogram:
  under the nondegenerate c=3 binomial relation pattern, the collision histogram has
  counts n, 2n, n(n-7) at deltas 24n-18, 90, 36.
```

That is the next real proof/refutation target.
