# #466 R199: shifted-quarter tower consumer

Status: deterministic consumer.

R198 showed the shifted-Cauchy shortcut:

```text
sum exp(left/8) exp(right/8) <= sum exp(left/4)
```

when the right child quarter sum is no larger than the left child quarter sum. R199 wires this
directly to the R168 parent tail-MGF consumer.

Lean artifact:

`_R199ShiftedQuarterTowerConsumer.lean`

Main theorem:

```text
parent_i <= left_i + right_i
sum exp(right_i/4) <= sum exp(left_i/4)
sum exp(left_i/4) <= 2 |s|
------------------------------------------------
DyadicTailMGFBound parent
```

Verified:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R199ShiftedQuarterTowerConsumer.lean
✅ OK
```

Consequence:

The dyadic tower no longer needs two independent quarter-MGF bounds or a separate covariance
estimate. It needs:

1. one child quarter-MGF bound `sum exp(left/4) <= 2 |s|`;
2. the quotient-shift/permutation fact that the right child has the same quarter sum as the left.

Thus the product-MGF route now concentrates on proving the one-level quarter-MGF bound using the
R196/R197 small-direct vs large-tail split.
