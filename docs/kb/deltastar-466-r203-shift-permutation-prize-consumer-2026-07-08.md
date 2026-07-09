# delta* #466 R203: shift-permutation prize consumer

Status: landed as a checked bridge consumer.

Artifacts:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R203ShiftPermutationPrizeConsumer.lean`
- Minor cleanup in `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R202ShiftPermutationQuarterSum.lean`
  removing an unnecessary decidable-equality assumption.

Lean checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R202ShiftPermutationQuarterSum.lean
✅ OK (18s)

scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R203ShiftPermutationPrizeConsumer.lean
✅ OK (20s)
```

Content:

- `dyadicTailMGF_of_shift_perm_quarter`: composes R202 with R200 to prove the
  R168 dyadic tail-MGF residual from:
  - parent subadditivity `parent_i ≤ left_i + right_i`;
  - a set-preserving permutation `e`;
  - pointwise child equality `right_i = left_{e i}`;
  - the one-child quarter-MGF budget for `left`.
- `prize_sq_of_shift_perm_quarter`: exposes the same permutation/equality datum
  directly at the final R168/S11 prize-square consumer.

Role in the live route:

R200 still had an abstract assumption comparing the right and left child quarter-MGF
sums. R203 removes that abstraction: future coding-theory work can prove the actual
quotient-shift/permutation statement and feed it directly to the prize consumer.

Still open after R203:

- Prove the finite-field child-spectrum quotient-shift/permutation identification.
- Prove the one-level quarter-MGF bound, likely via the small-direct / large normalized
  bulk-plus-spikes route.
