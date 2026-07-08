# #466 R200: shifted-quarter prize consumer

Status: deterministic consumer.

R199 made the tower-step target one child quarter-MGF bound plus a quotient-shift equality. R200
wires that all the way into the existing R168/S11 prize-square consumer.

Lean artifact:

`_R200ShiftedQuarterPrizeConsumer.lean`

Main chain:

```text
parent_i <= left_i + right_i
sum exp(right_i/4) <= sum exp(left_i/4)
sum exp(left_i/4) <= 2 |s|
------------------------------------------------
DyadicTailMGFBound parent
------------------------------------------------
R168/S11 prize-square bound
```

Verified:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R200ShiftedQuarterPrizeConsumer.lean
✅ OK
```

Large-anchor sanity:

```text
python3 scripts/probes/probe_r199_vectorized_large_anchor_tail.py --only-small --chunk 8192
max_positive_excess=0
```

Rows:

```text
n=256 p=16778497 M=65541 excess=-3.944 mgf1/4=1.4113
n=256 p=16780289 M=65548 excess=-9.002 mgf1/4=1.4101
```

Remaining proof inputs:

1. Prove the actual dyadic child lists are quotient shifts/permutations, giving equal quarter sums.
2. Prove the one-level quarter-MGF bound `sum exp(X/4) <= 2M`, using:
   - `M < 32`: finite direct certificates;
   - `M >= 32`: R189/R190/R194/R195/R197 large-index tail route.

This is still open, but the deterministic tower-to-prize chain now exposes exactly those two
finite-field analytic inputs.
