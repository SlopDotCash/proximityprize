# Issue #464: slackened profile-fiber dominance

Date: 2026-06-26.

Status: **new proof socket and critical essay**, not a delta-star proof.

## Thesis

The exact profile-fiber-max route is honest but brittle.  It asks for a representative `rep p`
that is a true bad-scalar maximizer inside every used profile fiber.  A more flexible route is:

```text
every stack in profile p has bad count
  <= bad count of rep p + slack p,
and
bad count of rep p + slack p <= B.
```

This is the right shape for a possible anti-resonance or stability theorem.  Instead of proving
that the proposed representative is exactly worst in its fiber, one can prove that all stacks in
that fiber differ from it by a controlled additive slack.  If the slack is smaller than the prize
budget margin, this still feeds the open-core incidence bound.

## Lean Socket

The new frontier file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberSlackDominance.lean
```

It introduces:

```lean
ProfileFiberSlackDominates
ProfileFiberSlackBudgeted
ProfileFiberSlackCertificate
```

The main consumers are:

```lean
worstCaseIncidenceBounded_of_profileFiberSlack
worstCaseIncidenceBounded_of_profileFiberSlackCertificate
deltaStar_pin_of_profileFiberSlack
deltaStar_pin_of_profileFiberSlackCertificate
```

The exact scanner/refutation forms are:

```lean
not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
profileFiberSlackDominates_iff_no_stack_exceeds_slack
not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
profileFiberSlackBudgeted_iff_no_usedProfile_budget_lt
not_profileFiberSlackCertificate_iff_exists_stack_exceeds_slack_or_budget_lt
```

So the slack-profile certificate fails for exactly two concrete reasons:

```text
1. some stack exceeds rep(profile u) plus the advertised slack;
2. some used profile has rep p plus slack p above B.
```

## Why This Is A Different Attack

Earlier profile files formalize exact fiber maximizers.  Those are enough, but a scanner can refute
them by finding one same-profile stack that beats the representative by one.

The slack route tolerates such local beaters.  A beater is fatal only if it beats the representative
by more than the declared slack.  This gives a potential middle path between:

```text
constant profile -> global maximizer problem returns;
identity profile -> all-stack budget problem returns;
exact fiber maxima -> too rigid for coarse analytic profiles.
```

The hoped-for new theorem would be a **fiber oscillation bound**:

```text
inside each profile fiber, bad-scalar counts have small diameter.
```

That is not the same as a Paley sup-norm bound if the profile is chosen well; it is a statement that
the missing phase information left after profiling cannot move the MCA bad-scalar count by more than
the available slack.

## PDF Sweep Verdict

The local library currently contains 337 PDFs.  The fresh sample for this loop included:

```text
LargeValuesMixedCharacterSums-2603.12159.pdf
Chattopadhyay-BurgessBoundsCharSums-Fpn-2602.22167.pdf
arxiv-2604.06513-NatureSpectrumGeneralizedPaleyGraphs.pdf
Szabo-LowerBoundHighMomentsCharacterSums-2409.13436.pdf
Aoki-GaussianPeriodsShanksCubic-2509.11137.pdf
Cornelissen-AsymptoticMahlerMeasureGaussianPeriods-2507.09303.pdf
arxiv-2601.07137-KoppartyNoisyCharacterValues.pdf
arxiv-2604.26989-SubgroupsFiniteFieldsCapSets.pdf
```

The result is still negative for the prize floor:

- Large-value Fekete/mixed-character distribution gives tail laws in an averaging over arcs.  It is
  not a worst-stack MCA incidence theorem.
- Burgess-type box cancellation over `F_{p^n}` gives cancellation once a structured box has enough
  volume.  The #464 floor needs thin-subgroup and worst-profile control, not just a high-volume box
  estimate.
- Generalized Paley graph spectrum papers identify the Gaussian-period dictionary and useful Waring
  structure.  They do not give the needed `sqrt(n log(p/n))` worst-period or profile-fiber slack
  bound.
- High-moment lower bounds show large values are unavoidable in character-sum families.  They are a
  warning against replacing worst-stack control by moment heuristics.
- Gaussian-period arithmetic/Mahler-measure papers give structural and asymptotic information about
  periods, but not a uniform MCA bad-scalar bound over stack profiles.
- Noisy-character recovery is algorithmic Weil/Stepanov machinery for low-degree polynomial
  characters.  It suggests possible proof technology but does not match the multiplicative-subgroup
  period regime directly.
- Subgroup cap-set examples support the philosophy that multiplicative structure can suppress some
  additive configurations, but the statements are exact small-configuration exclusions, not the
  uniform bad-scalar incidence budget needed here.

## Critical Failure Of The Previous Exact-Max Essay

The exact fiber-max route implicitly asks for a canonical worst stack inside every profile fiber.
That is probably too rigid for the Paley/BGK cone.  The sampled literature repeatedly gives
distributional, spectral, energy, or special-configuration facts.  These facts are compatible with
small fiber oscillation, but they rarely select an exact maximizer.

The corrected conjectural tool is:

```text
Profile Oscillation Lemma:
For a profile retaining the right period/Jacobi/resonance invariants, the MCA bad-scalar count is
stable inside each fiber up to slack o(B), or at least up to the remaining floor-budget margin.
```

This would let the proof tolerate local profile imperfections and still feed the delta-star pin via
`ProfileFiberSlackCertificate`.

## Next Red-Team Test

A proposed profile must now pass three checks:

```text
1. compression: #P is genuinely smaller than the stack universe;
2. oscillation: every fiber has small bad-count diameter, or every stack is within slack of rep p;
3. budget: rep p plus slack p is below the MCA budget for every used profile.
```

If (1) fails, the profile is the identity route in disguise.  If (2) fails, scanners should return a
stack exceeding its allowance via
`not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack`.  If (3) fails, the route is just an
above-budget representative.

This does not close the floor.  It sharpens the next mathematical target from "find exact
representatives" to "prove a fiber oscillation theorem with enough slack margin."
