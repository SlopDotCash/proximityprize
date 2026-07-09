# δ* #466 — R182 tower product-budget consumer (2026-07-08)

## Purpose

R181 showed that a crude tower-step inequality may already be enough for the
R168 MGF route.  R182 wires that shape into Lean.

## Lean Update

Updated:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```

New theorem:

```text
dyadicTailMGF_of_tower_product_budget
```

Statement shape:

```text
If parent_i ≤ left_i + right_i
and Σ_i exp(left_i/8) exp(right_i/8) ≤ 2 |s|,
then DyadicTailMGFBound s parent.
```

## Intended Arithmetic Instantiation

For the dyadic tower split, a parent period is `a+b`.  With
`σ²_parent = 2σ²_child`, the elementary inequality

```text
|a+b|² ≤ 2(|a|²+|b|²)
```

gives the required normalized bound

```text
parent_i ≤ left_i + right_i.
```

The remaining mathematical target is therefore the paired child product-budget
estimate.  R181 measured that this budget is loose but still well below the
R168 threshold.

Verified:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R168DyadicTailEnvelopeConsumer.lean
```
