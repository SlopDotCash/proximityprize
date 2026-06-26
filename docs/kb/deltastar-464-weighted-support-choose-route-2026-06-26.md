# delta* #464: weighted support-choose is the next honest singleton socket

## Thesis

The previous codeword-indexed support-ratio cover step proved that fixed-codeword coordinate
overlap is exhausted.  The cover injects into support subsets:

```text
cover(c) <= choose(#support(u1), a - #zeroAgreement(c)).
```

The first way to consume this was a uniform cap `S` for every appearing codeword.  That is useful
as a scanner, but it is arithmetically blunt: it replaces every codeword's actual zero-agreement
profile by the worst cap and then pays

```text
#appearingCodewords * S.
```

The next honest refinement is to pay the actual cap codeword-by-codeword:

```text
sum_{c appearing} choose(#support(u1), a - #zeroAgreement(c)).
```

This is still not a floor proof.  It is the strongest coordinate-packing accounting now available
inside the singleton-defect route before invoking scalar-level Reed-Solomon rigidity or a
second-witness theorem.

## What was formalized

`LineListCodewordSingletonSupportRatio.lean` now defines the weighted support-choose cost:

```lean
codewordSupportChooseWeight
```

and proves that it controls the singleton defect on safe lines:

```lean
singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe
lineBadScalars_card_le_of_weight_add_codewordSupportChoose_le_two_mul
```

The route has uniform production plumbing:

```lean
UniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportChooseWeightBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportChooseWeightBudget
```

It is also formally a refinement of the older uniform support-choose route:

```lean
codewordSupportChooseWeight_le_lineAppearingCodewords_card_mul
uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_of_codewordSupportChooseBudget
```

So any proof that fits the older `#appearing * S` arithmetic also fits the weighted route, but the
weighted route can be strictly better when appearing codewords have different zero-agreement
profiles.

Finally, failed production has an exact weighted scanner:

```lean
not_uniformLargeZeroSafeWeightPlusCodewordSupportChooseBudgeted_iff_exists_weight_gt
exists_largeZero_safe_codewordSupportChooseWeight_gt_of_not_uniformLineBadScalarsBudgeted
```

Thus, with the support-eligible branch, support arithmetic, and zero-direction safety fixed, a
failed production attempt returns a large-zero safe line where

```text
2B < puncturedZeroStratifiedLineWeight
     + sum_{c appearing} choose(#support(u1), a - #zeroAgreement(c)).
```

This is a sharper failure object than a single overfull codeword cap.

## Why this does not close the floor

The weighted route spends all pure coordinate-packing information from the current support-ratio
cover.  It still ignores the uniqueness clause except through the singleton-defect decomposition:
for each singleton scalar, it knows there is exactly one witness codeword, but it does not use the
absence of a second witness to force algebraic consequences.

That matters because the support-choose term can remain enormous.  If many appearing codewords
have small zero agreement, the weighted sum still resembles a binomial support-subset census.  No
new cancellation, interpolation dependence, or Paley/Gauss-period input appears in the proof.  It
therefore does not bypass the BGK/Paley wall by itself; it only sharpens the finite line-list
socket that a future bypass would have to exploit.

## Revised target

The next nonredundant theorem should attack one of two statements.

First, a **profile concentration theorem**:

```text
On every large-zero safe bad line, appearing codewords with small #zeroAgreement(c)
are rare enough that codewordSupportChooseWeight fits the production budget.
```

This would make the weighted route a real floor proof, but it needs new structure controlling the
distribution of zero-agreement profiles among actual appearing Reed-Solomon codewords.

Second, a **singleton rigidity theorem**:

```text
If codewordSupportChooseWeight is above budget, then some singleton scalar
actually has a second witness, or the line belongs to an explicitly classified exceptional family.
```

This is the more likely mathematical route.  It would spend the uniqueness condition that all
current coordinate-packing estimates throw away.  The natural object is no longer a cover-card
bound; it is an interpolation graph on singleton scalars and their unique witness codewords.

## Verdict

The uniform support-choose cap was too coarse.  The weighted support-choose route is a real
refinement and is now wired into production, with an exact scanner exposing the remaining
overfull object.  But it is still a coordinate-accounting theorem.  If it fails, the next essay
should stop trying to squeeze the support-choose census and instead formalize a second-witness or
interpolation-rigidity graph that uses the missing uniqueness information.
