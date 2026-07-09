# δ* #466 — R185 tower AM-GM MGF consumer (2026-07-08)

## Purpose

R184 observed that the R182 paired product budget is controlled by a higher-rate
child MGF.  R185 formalizes a simple version of that reduction in Lean using
AM-GM.

## Lean Update

Updated:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```

New theorem:

```text
dyadicTailMGF_of_tower_amgm_mgf
```

Statement shape:

```text
If parent_i ≤ left_i + right_i,
and Σ_i exp(left_i/4) ≤ 2 |s|,
and Σ_i exp(right_i/4) ≤ 2 |s|,
then DyadicTailMGFBound s parent.
```

The proof is pointwise AM-GM:

```text
exp(left/8) exp(right/8)
  ≤ (exp(left/4) + exp(right/4)) / 2.
```

## Meaning

The tower route now has a cleaner sufficient residual:

```text
child MGF at rate 1/4 ≤ 2
```

for both child halves of the dyadic split.  Together with the normalized parent
bound from sigma doubling and `|a+b|² ≤ 2(|a|²+|b|²)`, this lands the R168 MGF
residual for the parent.

Verified:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```
