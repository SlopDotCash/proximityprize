# Issue #464: profile granularity endpoints

Date: 2026-06-26.

Status: **critical refinement**, not a delta-star proof.

## Thesis

The profile/oscillation route has two useless endpoints:

```text
constant profile  -> one giant fiber, global pairwise oscillation problem;
injective profile -> no compression, original all-stack incidence problem.
```

The previous compression note
`docs/kb/deltastar-464-profile-compression-tradeoff-2026-06-25.md` proved the cardinal version:
an injective profile has profile space at least as large as the stack universe, while any small
profile must merge many stacks into large fibers.

This pass adds the proof-theoretic endpoint inside
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean`.

## Lean Additions

For an injective profile whose representatives lie in used fibers:

```lean
rep_profile_eq_of_injective
profileFiberOscillationBounded_zero_of_injective
profileFiberSlackDominates_zero_of_injective
profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberSlackCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberOscillationCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
```

The key point is:

```text
profile injective + rep in fiber
  => rep (profile u) = u
```

So zero-slack profile budgeting is exactly:

```text
for every stack u, StackBadCount u <= B,
```

which is the original `WorstCaseIncidenceBounded` hypothesis.

## Consequence

The profile route is now squeezed from both sides:

```text
too coarse:
  constant-profile oscillation = global pairwise bad-count diameter;

too fine:
  injective zero-slack profile = original all-stack incidence bound;

useful:
  non-injective but not too coarse, with a real same-fiber oscillation theorem.
```

That last line is the only place where the route can still contain new mathematics.  A successful
profile must merge distinct stacks while retaining enough algebraic structure to prove that all
same-profile bad-scalar counts stay within the advertised slack.

## Literature Status

The current literature trail still points back to the usual Paley/character-sum faces: generalized
Paley spectra, Gaussian periods, Burgess/subgroup estimates, high moments, and large-value tails.
Those inputs motivate possible profile features, but they do not currently provide a theorem with
output type:

```text
same profile u v -> StackBadCount u <= StackBadCount v + slack(profile u).
```

So this is not a closure.  It is a sharper target for the next loop: either invent a compressed
profile with a genuine fiber-oscillation proof, or accept that the profile route has collapsed back
to BGK/Paley worst-period control.
