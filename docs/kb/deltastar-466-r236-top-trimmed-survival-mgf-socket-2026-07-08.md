# R236 top-trimmed survival MGF socket

Date: 2026-07-08
Issue: #466 / Proximity Prize

## Purpose

R231-R235 isolate the live analytic shape:

```text
pay a top set T exactly;
prove a residual survival tail on s \ T;
combine exact top payment + residual envelope in the S11 layer-cake budget.
```

R236 drafts the generic finite-carrier Lean socket for this accounting:

```text
TopTrimmedBound s T t Bres theta
  = #{b in T ∩ s : theta <= t b} + Bres theta
```

and the theorem shape:

```text
if #{b in s \ T : theta <= t b} <= Bres theta
and Σ_theta δ(theta) * TopTrimmedBound(...) <= A * |s|,
then MGFBound s t A c.
```

This is the abstract formal endpoint needed for the top-five quotient route.

## Draft Artifact

Draft file exists locally but is not staged:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R236TopTrimmedSurvivalMGF.lean
```

Main intended declarations:

```text
TopTrimmedBound
survival_count_le_topTrimmedBound
mgfBound_of_topTrimmed_survival_count_ceiling
two_mgfBound_of_topTrimmed_survival_count_ceiling
```

## Verification Status

Attempted:

```bash
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R236TopTrimmedSurvivalMGF.lean
```

Blocked before elaborating the file:

```text
missing Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots.olean
```

Attempted repair:

```bash
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfS11_survival_to_mgf
```

but the checkout build lock was held for over a minute, so the queued build was
interrupted to avoid contributing to build contention.

## Next Step

Once the mathlib cache is repaired, run `pg-iterate` on R236 and fix any actual
elaboration errors.  Until then, R236 is a design draft, not a landed theorem.
