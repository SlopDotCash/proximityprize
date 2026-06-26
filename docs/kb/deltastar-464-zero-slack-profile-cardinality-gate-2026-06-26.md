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

## Lean Surface

In `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`:

```lean
BadCountInjectiveOn
profile_injOn_of_profileBadCountFiberConstant_of_badCountInjectiveOn
card_le_profileCard_of_profileBadCountFiberConstant_badCountInjectiveOn
not_profileBadCountFiberConstant_of_profileCard_lt_badCountInjectiveOn
not_profileBadCountRepresented_of_profileCard_lt_badCountInjectiveOn
not_profileFiberOscillationBounded_zero_of_profileCard_lt_badCountInjectiveOn
```

The central theorem is:

```text
ProfileBadCountFiberConstant F C delta profile
+ BadCountInjectiveOn F C delta U
=> U.card <= Fintype.card P
```

Equivalently, if `Fintype.card P < U.card`, then zero-slack fiber constancy, representative
bad-count factorization, and zero same-profile oscillation all fail for that profile.

## Consequence

This is a finite refutation socket for concrete profile proposals.  A scanner no longer has to find
two same-profile stacks with different counts directly.  It can first produce more distinct
bad-count values than the candidate profile has labels; that already proves the profile cannot be a
zero-slack invariant.

Positive-slack profiles are not refuted by this gate.  They still need a genuine oscillation theorem
that pays for the count variation inside the large fibers.
