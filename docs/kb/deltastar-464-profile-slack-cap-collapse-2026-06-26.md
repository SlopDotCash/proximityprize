# Issue #464: profile slack collapses to profile caps

Date: 2026-06-26.

Status: **critical refinement**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The previous loop introduced a slackened profile-fiber certificate:

```lean
ProfileFiberSlackDominates F C δ profile rep slack
ProfileFiberSlackBudgeted F C δ profile rep slack B
```

The hope was pragmatic: a coarse profile might not have exact fiber-max representatives, but perhaps
each fiber is within a controlled additive slack of a chosen representative.  That is still a useful
scanner socket.  This pass proves the honest critique: the slack certificate is not a new proof
principle.  It is exactly the old profile-cap interface with the cap

```text
cap(p) = StackBadCount(rep p) + slack(p).
```

## Lean Additions

In `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`:

```lean
slackCap
UsedProfileBudgeted
profileCaps_slackCap_iff_profileFiberSlackDominates
usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted
profileFiberSlackCertificate_iff_slackCap_profileCaps_usedBudgeted
profileBudgeted_slackCap_iff_profileFiberSlackBudgeted_of_all_used
```

The main equivalence is:

```text
ProfileFiberSlackCertificate F C δ profile rep slack B
  iff
ProfileCaps F C δ profile (slackCap C δ rep slack)
  and
UsedProfileBudgeted profile (slackCap C δ rep slack) B.
```

If every profile label is used, the used-profile budget is literally the existing
`ProfileBudgeted` condition for `slackCap`.

## Critique

This kills the optimistic reading of the slack tool.  Slack does not bypass the need for a universal
profile theorem.  It only changes which cap function must be proved:

```text
old cap route:   bad(u) <= cap(profile u)
slack route:     bad(u) <= bad(rep(profile u)) + slack(profile u)
```

The second line is the first line with a data-dependent cap.  Therefore a claimed slack proof can
fail in the same two ways as the profile-cap route:

1. a stack exceeds the induced cap of its profile;
2. a used profile's induced cap exceeds the budget.

That is exactly what the existing negative lemmas in `_ProfileFiberSlackDominance.lean` expose.

## What Still Helps

The slack form is still valuable for experiments because it suggests a measurable certificate:
choose representatives, measure profile-wise gaps, and see whether

```text
max_profile (bad(rep p) + slack(p)) <= B.
```

If a scanner finds small slack on the verified floor rungs, that is evidence for a normal-form
theorem.  But the proof obligation remains universal: explain why every stack in every profile fiber
is within the advertised slack.  That is algebraic/incidence structure, not a consequence of the
least-prime floor localization.

So the #464 floor remains where the issue dossier says it is: either prove a genuine universal
stack/profile normal form, or prove the thin-subgroup Paley/BGK period bound.  This loop sharpens the
former target and prevents the slack vocabulary from hiding the same open content.

## Validation

Direct iteration passed:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean
```

The new axiom audits report only the expected Lean foundations and no `sorryAx`.
