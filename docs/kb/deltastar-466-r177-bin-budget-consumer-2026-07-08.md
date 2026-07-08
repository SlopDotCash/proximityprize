# δ* #466 — R177 bin-budget compensation consumer (2026-07-08)

## Purpose

R176 found a dyadic polarization pattern: extra high-tail mass is accompanied
by extra near-zero mass, and the R168 MGF budget remains small.  R177 wires
that compensation strategy into Lean.

## Lean Update

Updated:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```

New theorem:

```text
dyadicTailMGF_of_bin_budget
```

Statement shape:

```text
If each b ∈ s is assigned to a bin binOf(b),
and exp(t_b/8) ≤ E(binOf(b)),
and Σ_b E(binOf(b)) ≤ 2 |s|,
then DyadicTailMGFBound s t.
```

## Meaning

This is the Lean-facing endpoint for a polarization proof.  Instead of proving
a monotone tail theorem directly, one may partition the spectrum into bins and
show the high-tail bins are paid for by enough low-bin mass that the total
exponential budget remains below `2 |s|`.

Verified:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```
