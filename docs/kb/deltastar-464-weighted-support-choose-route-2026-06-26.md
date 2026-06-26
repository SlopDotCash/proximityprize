# delta* #464: weighted support-choose and the sharper denominator baseline

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

Follow-up: the scalar accounting baseline is sharper than this coordinate-packing census.  The
weighted denominator cost pays

```text
sum_{c appearing} #support(u1)/(a - #zeroAgreement(c)).
```

Lean now proves this weighted denominator budget controls singleton defects directly and sits
below weighted support-choose on zero-safe lines.  Thus weighted support-choose remains useful as
cover control, but the scalar route to beat is the weighted denominator budget.

## What was formalized

`LineListCodewordSingletonSupportRatio.lean` defines the weighted support-choose cost, while
`LineListCodewordSingletonSupportDivWeight.lean` defines the weighted denominator cost:

```lean
codewordSupportDivWeight
codewordSupportChooseWeight
```

and proves that both control the singleton defect on safe lines:

```lean
singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe
singletonBadScalarDefect_le_codewordSupportChooseWeight_of_zeroSafe
lineBadScalars_card_le_of_weight_add_codewordSupportDiv_le_two_mul
lineBadScalars_card_le_of_weight_add_codewordSupportChoose_le_two_mul
```

The denominator route has uniform production plumbing and an exact scanner:

```lean
UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportDivWeightBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_iff_exists_weight_gt
exists_largeZero_safe_codewordSupportDivWeight_gt_of_not_uniformLineBadScalarsBudgeted
```

Weighted support-choose implies that sharper denominator budget:

```lean
codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe
uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_codewordSupportChooseWeightBudget
```

The support-choose route still has its own production plumbing:

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

This is a sharper failure object than a single overfull codeword cap, but the denominator scanner
is the scalar-sharper obstruction:

```text
2B < puncturedZeroStratifiedLineWeight
     + sum_{c appearing} #support(u1)/(a - #zeroAgreement(c)).
```

## Why this does not close the floor

The weighted route spends all pure coordinate-packing information from the current support-ratio
cover.  It still ignores the uniqueness clause except through the singleton-defect decomposition:
for each singleton scalar, it knows there is exactly one witness codeword, but it does not use the
absence of a second witness to force algebraic consequences.

That matters because the support-choose term can remain enormous, and even the denominator term
uses only heavy-scalar support accounting.  If many appearing codewords have small zero agreement,
the weighted support-choose sum still resembles a binomial support-subset census, while the
weighted denominator sum is the actual scalar baseline.  No new cancellation, interpolation
dependence, or Paley/Gauss-period input appears in either proof.  They therefore do not bypass the
BGK/Paley wall by themselves; they only sharpen the finite line-list socket that a future bypass
would have to exploit.

## Revised target

The next nonredundant theorem should attack one of two statements.

First, a **profile concentration theorem**:

```text
On every large-zero safe bad line, appearing codewords with small #zeroAgreement(c)
are rare enough that codewordSupportDivWeight fits the production budget.
```

This would make the weighted route a real floor proof, but it needs new structure controlling the
distribution of zero-agreement profiles among actual appearing Reed-Solomon codewords.

Second, a **singleton rigidity theorem**:

```text
If codewordSupportDivWeight is above budget, then some singleton scalar
actually has a second witness, or the line belongs to an explicitly classified exceptional family.
```

This is the more likely mathematical route.  It would spend the uniqueness condition that all
current coordinate-packing estimates throw away.  The natural object is no longer a cover-card
bound; it is an interpolation graph on singleton scalars and their unique witness codewords.

## Verdict

The uniform support-choose cap was too coarse, and weighted support-choose is still not the
scalar-sharp endpoint.  The weighted denominator route is now wired into production, and
support-choose implies it.  If the denominator scanner fails, the next essay should stop trying to
squeeze support-subset censuses and instead formalize a second-witness or interpolation-rigidity
graph that uses the missing uniqueness information.
