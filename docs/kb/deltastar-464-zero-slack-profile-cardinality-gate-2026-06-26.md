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
profileBadCountImageCovered_of_profileFiberOscillation
stackBadCountImage_card_le_sum_profileFiberOscillationIntervals
not_profileFiberOscillationBounded_of_sum_intervalCard_lt_stackBadCountImage
card_Icc_sub_add_le_two_mul_add_one
stackBadCountImage_card_le_sum_profileFiberOscillationSlack
stackBadCountImage_card_le_profileCard_mul_uniformOscillationSlack
not_profileFiberOscillationBounded_of_sum_slack_lt_stackBadCountImage
not_profileFiberOscillationBounded_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
stackBadCountImage_card_le_sum_profileFiberOscillationCertificateSlack
stackBadCountImage_card_le_profileCard_mul_uniformOscillationCertificateSlack
not_profileFiberOscillationCertificate_of_sum_slack_lt_stackBadCountImage
not_profileFiberOscillationCertificate_of_profileCard_mul_uniformSlack_lt_stackBadCountImage
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

For the existing oscillation certificate, representatives in their fibers plus
`ProfileFiberOscillationBounded` produce the concrete cover

```text
Icc (StackBadCount (rep p) - slack p) (StackBadCount (rep p) + slack p)
```

for each profile `p`.  The theorem
`stackBadCountImage_card_le_sum_profileFiberOscillationIntervals` records the resulting global
bound, and the negated interval theorem refutes a proposed oscillation certificate when those
intervals have too little total cardinality.

The interval-card follow-up removes the representative-count centers from the budget:

```text
(StackBadCountImage F C delta).card <= sum_p (2 * slack p + 1)
```

and, if every `slack p <= S`, the uniform form gives

```text
(StackBadCountImage F C delta).card <= Fintype.card P * (2 * S + 1).
```

Thus a scanner can refute a same-profile oscillation certificate from only the profile count and
slack budget, without evaluating each representative-centered interval.

The certificate-level forms package the same tests for the bundled
`ProfileFiberOscillationCertificate`, so consumers can refute the full structured certificate
directly when the summed or uniform slack budget is smaller than the realized bad-count image.

## Consequence

This is a finite refutation socket for concrete profile proposals.  A scanner no longer has to find
two same-profile stacks with different counts directly.  It can first produce more distinct
bad-count values than the candidate profile has labels; that already proves the profile cannot be a
zero-slack invariant.

Positive-slack profiles are not refuted by the zero-slack label gate alone.  They now need either a
finite cover large enough to account for the global bad-count image, or a genuine oscillation theorem
that pays for the count variation inside the large fibers.
