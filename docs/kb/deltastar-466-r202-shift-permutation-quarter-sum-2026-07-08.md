# delta* #466 R202: shift-permutation quarter-sum consumer

Status: landed as a checked finite-set consumer.

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R202ShiftPermutationQuarterSum.lean`

Lean check:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R202ShiftPermutationQuarterSum.lean
✅ OK (18s)
```

Content:

- `sum_comp_perm_eq`: a permutation preserving a finite index set preserves finite sums.
- `quarter_sum_eq_of_perm`: if the right-child score vector is the left-child score vector
  composed with such a permutation, the quarter-MGF sums are equal.
- `quarter_sum_le_of_perm`: the equality immediately supplies the `right ≤ left`
  side-condition used by the shifted-quarter R199/R200 prize route.

Role in the live route:

R199/R200 reduce one branch of the shifted-quarter tower to a right-child quarter-sum
comparison. R202 isolates the purely combinatorial proof obligation: once the quotient-shift
identification is expressed as a set-preserving permutation of the sampled indices, the
quarter-MGF comparison is automatic.

Open after R202:

- Prove the actual quotient-shift/permutation identification for the coding-theory child
  spectra.
- Prove the one-level quarter-MGF bound, split into the small direct census and the large
  normalized bulk-plus-two-tail/spike-mass branch.
