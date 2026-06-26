# Issue #464: zero-slack profiles must separate distinct bad counts

Date: 2026-06-26.

Status: **scanner guardrail**, not a delta-star proof.

## Thesis

The zero-slack profile route asks for a compressed invariant

```lean
profile : WordStack A (Fin 2) iota -> P
```

such that `StackBadCount` is constant on each profile fiber.  This pass adds the missing
cardinality pressure for that claim: if a scanner finds a finite family `U` of stacks whose
bad-scalar counts are pairwise distinct, then any zero-slack profile must be injective on `U`.

So a proposed profile with fewer labels than `#U` cannot support zero-slack bad-count constancy.

The follow-up globalizes this scanner.  Let `StackBadCountImage F C delta` be the finite image of
`StackBadCount` over the whole stack universe.  Any zero-slack profile must have at least that many
labels:

```text
ProfileBadCountFiberConstant F C delta profile
=> (StackBadCountImage F C delta).card <= Fintype.card P
```

Thus a profile whose type has fewer labels than the number of realized bad-count values is refuted
without first choosing a separate scanner subset `U`.

## Lean Surface

In `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`:

```lean
BadCountInjectiveOn
profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
StackBadCountImage
stackBadCountImage_card_le_profileCard_of_profileBadCountFiberConstant
not_profileBadCountFiberConstant_of_profileCard_lt_stackBadCountImage
not_profileBadCountRepresented_of_profileCard_lt_stackBadCountImage
not_profileFiberOscillationBounded_zero_of_profileCard_lt_stackBadCountImage
ProfileBadCountImageCovered
stackBadCountImage_card_le_sum_profileBadCountCover
not_profileBadCountImageCovered_of_sum_cover_lt_stackBadCountImage
```

The central theorem is:

```text
ProfileBadCountFiberConstant F C delta profile
+ BadCountInjectiveOn F C delta U
=> U.card <= Fintype.card P
```

Equivalently, if `Fintype.card P < U.card`, then zero-slack fiber constancy, representative
bad-count factorization, and zero same-profile oscillation all fail for that profile.

The global theorem replaces `U.card` by `(StackBadCountImage F C delta).card` and gives the same
three refutations.  This is the exact profile-label lower bound forced by a zero-slack invariant.

The cover form is the positive-slack analogue.  If each profile label `p` supplies a finite
`cover p : Finset Nat` containing every bad-count value realized by stacks with profile `p`, then

```text
(StackBadCountImage F C delta).card <= sum_p (cover p).card
```

Thus finite positive-slack explanations also face an image-size test: if the total cover size is
smaller than the realized bad-count image, the proposed fiber-count cover is false.

## Consequence

This is a finite refutation socket for concrete profile proposals.  A scanner no longer has to find
two same-profile stacks with different counts directly.  It can first produce more distinct
bad-count values than the candidate profile has labels; that already proves the profile cannot be a
zero-slack invariant.

Positive-slack profiles are not refuted by the zero-slack label gate alone.  They now need either a
finite cover large enough to account for the global bad-count image, or a genuine oscillation theorem
that pays for the count variation inside the large fibers.
