# #466 R308: depth-uniform char-zero shadow floor

Date: 2026-07-09

## What landed

`Frontier/_R308DepthUniformShadowFloor.lean` generalizes the R306/R307 depth-3
char-zero shadow factorization to every moment depth `r`.

Main declarations:

```text
gsumR_eq_evalVec_tupleVec
repRF_eq_sum_NR
shadowR_energy_le_depthR_energy
depthR_energy_eq_of_shadow_injective
```

The file proves that the field-level `r`-sum factors through an integer shadow
vector, that field fibers are pushforwards of the char-zero histogram, and that:

```text
sum_v NR(v)^2 <= sum_c repRF(c)^2.
```

It also proves equality under shadow injectivity.

## Meaning

This isolates the arithmetic obstruction at arbitrary depth: the char-zero
shadow energy is a floor, and any extra char-`p` depth-`r` energy is exactly
collision mass from distinct integer shadows collapsing in the field.

## Validation

Passed:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R308DepthUniformShadowFloor.lean
```
