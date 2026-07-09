# R234: rank-sum residual Lean socket

Status: formal socket added; verification currently blocked by local mathlib
cache lock.

## File

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R234RankSumResidualMGFConsumer.lean
```

## Formal shape

The theorem

```text
nonzeroNormalizedSqQuarterMGFResidual_of_topRank_residual_tail
```

exposes the R234 proof target on the raw nonzero-frequency carrier:

1. choose a marked top-rank set `T`;
2. prove a direct top contribution bound

```text
sum_{b in topNonzeroFreqs T} exp((1/4) * X_b) <= Atop;
```

3. prove a residual staircase domination on

```text
residualNonzeroFreqs T = nonzeroFreqs \ T;
```

4. prove residual survival-count ceilings `B(theta)` on that residual carrier;
5. prove the finite weighted budget

```text
Atop + sum_theta delta(theta) * B(theta)
  <= 2 * #nonzeroFreqs.
```

The conclusion is the existing

```text
NonzeroNormalizedSqQuarterMGFResidual ψ G σ.
```

## Why this matters

This is the Lean-facing endpoint for the R234 numerical closure:

```text
top-8 direct rank-sum cap + residual half-band tail
```

after finite/direct exception handling of exact MGF-failing resonances.

The file does not prove the analytic rank-sum or residual-tail inputs.  It
only packages the finite layer-cake bookkeeping so those hard inputs have a
clean target.

## Verification status

Attempted command:

```bash
scripts/pg-iterate.sh -q \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R234RankSumResidualMGFConsumer.lean
```

Observed failure:

```text
error: object file ... Mathlib/FieldTheory/RatFunc/Basic.olean does not exist
```

The failure occurred at the import line before checking this file's theorem.
The sanctioned repair command

```bash
./scripts/lake-locked.sh exe cache get
```

was blocked by the existing checkout lock `17412`, matching the cache-lock
issue seen while checking R229.  No Lean type error from the new R234 theorem
has been observed yet.
