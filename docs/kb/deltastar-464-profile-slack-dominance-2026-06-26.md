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
ProfileRepresentativeInFiber
ProfileFiberOscillationBounded
ProfileFiberOscillationCertificate
```

The main consumers are:

```lean
worstCaseIncidenceBounded_of_profileFiberSlack
worstCaseIncidenceBounded_of_profileFiberSlackCertificate
worstCaseIncidenceBounded_of_profileFiberOscillationCertificate
deltaStar_pin_of_profileFiberSlack
deltaStar_pin_of_profileFiberSlackCertificate
deltaStar_pin_of_profileFiberOscillationCertificate
```

The structured oscillation route proves:

```lean
profileFiberSlackDominates_of_fiberOscillation
profileFiberSlackCertificate_of_profileFiberOscillationCertificate
```

So a proof can now enter through same-profile oscillation:

```text
1. used representatives are actually in their profile fibers;
2. same-profile bad-scalar counts differ by at most slack p, one-sided;
3. representative bad count plus slack is within B.
```

The file also records the constant-profile endpoint:

```lean
profileRepresentativeInFiber_of_constant
profileFiberSlackDominates_constant_iff_forall_le_rep_add_slack
profileFiberOscillationBounded_constant_iff_global_pairwise_bound
not_profileFiberOscillationBounded_constant_iff_exists_global_pair_exceeds_slack
profileRepresentativeInFiber_identity
profileFiberSlackDominates_identity_zero
profileFiberOscillationBounded_identity_zero
profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded
profileFiberSlackCertificate_identity_zero_iff_worstCaseIncidenceBounded
profileFiberOscillationCertificate_identity_zero_iff_worstCaseIncidenceBounded
rep_profile_eq_of_injective
profileFiberOscillationBounded_zero_of_injective
profileFiberSlackDominates_zero_of_injective
profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberSlackCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberOscillationCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
ProfileBadCountRepresented
profileBadCountRepresented_of_zero_oscillation
profileFiberOscillationBounded_zero_of_profileBadCountRepresented
profileFiberOscillationBounded_zero_iff_profileBadCountRepresented_of_repInFiber
worstCaseIncidenceBounded_of_profileBadCountRepresented_budget
deltaStar_pin_of_profileBadCountRepresented_budget
profileFiberOscillationCertificate_zero_iff_profileBadCountRepresented_and_budget
not_profileBadCountRepresented_iff_exists_stack_count_ne
not_profileBadCountRepresented_and_zeroBudgeted_iff_exists_factor_miss_or_budget_lt
```

This is the formal warning that the coarsest possible profile recreates the global
representative/dominator problem: oscillation inside the one profile fiber is just a global pairwise
bad-count diameter bound.

The opposite endpoint is also formalized:

```lean
profileRepresentativeInFiber_identity
profileFiberSlackDominates_identity_zero
profileFiberOscillationBounded_identity_zero
profileFiberSlackBudgeted_identity_zero_iff_worstCaseIncidenceBounded
profileFiberSlackCertificate_identity_zero_iff_worstCaseIncidenceBounded
profileFiberOscillationCertificate_identity_zero_iff_worstCaseIncidenceBounded
```

There is also a general injective-profile endpoint:

```lean
rep_profile_eq_of_injective
profileFiberOscillationBounded_zero_of_injective
profileFiberSlackDominates_zero_of_injective
profileFiberSlackBudgeted_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberSlackCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
profileFiberOscillationCertificate_zero_iff_worstCaseIncidenceBounded_of_injective
```

So the identity profile, and more generally any injective profile with representatives in used
fibers and zero slack, is exactly the original all-stack incidence problem.  The two endpoints now
bracket the search: a profile that is too coarse requires global pairwise oscillation control, while
a profile that is too fine simply restates the target theorem stack by stack.

## 2026-06-26 Red-Team Correction: Slack Is A Cap Choice

The file now also formalizes the exact relation to the older profile-cap interface.  A slack
representative scheme induces the profile cap

```lean
slackCap C delta rep slack p =
  StackBadCount F C delta (rep p) + slack p
```

and proves:

```lean
profileCaps_slackCap_iff_profileFiberSlackDominates
usedProfileBudgeted_slackCap_iff_profileFiberSlackBudgeted
profileFiberSlackCertificate_iff_slackCap_profileCaps_usedBudgeted
profileBudgeted_slackCap_iff_profileFiberSlackBudgeted_of_all_used
```

So the slack route does not create a stronger theorem form.  It is a structured way to choose a
profile cap and then ask for the same two facts as before:

```text
1. every stack is below its assigned cap;
2. every used cap is within the incidence budget.
```

The only genuine mathematical gain can come from proving a useful stability theorem that produces
small slack for a compressed profile.  Without that theorem, the slack certificate is just the direct
profile-cap certificate written in representative-plus-error coordinates.

The exact scanner/refutation forms are:

```lean
not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack
profileFiberSlackDominates_iff_no_stack_exceeds_slack
not_profileFiberSlackBudgeted_iff_exists_usedProfile_budget_lt
profileFiberSlackBudgeted_iff_no_usedProfile_budget_lt
not_profileFiberSlackCertificate_iff_exists_stack_exceeds_slack_or_budget_lt
not_profileRepresentativeInFiber_iff_exists_usedProfile_rep_misses
not_profileFiberOscillationBounded_iff_exists_sameProfile_exceeds_slack
profileFiberOscillationBounded_iff_no_sameProfile_exceeds_slack
not_profileFiberOscillationCertificate_iff_exists_rep_misses_or_sameProfile_exceeds_or_budget_lt
profileRepresentativeInFiber_of_constant
profileFiberSlackDominates_constant_iff_forall_le_rep_add_slack
profileFiberOscillationBounded_constant_iff_global_pairwise_bound
not_profileFiberOscillationBounded_constant_iff_exists_global_pair_exceeds_slack
```

So the slack-profile certificate fails for exactly two concrete reasons:

```text
1. some stack exceeds rep(profile u) plus the advertised slack;
2. some used profile has rep p plus slack p above B.
```

The stronger oscillation certificate fails for exactly three concrete reasons:

```text
1. a used profile's representative is not actually in that profile fiber;
2. a same-profile pair has bad-count gap above the advertised slack;
3. a used representative-plus-slack allowance is above B.
```

The constant-profile endpoint is now formal too.  If `profile u = p0` for every stack, then
`ProfileFiberOscillationBounded` is exactly:

```text
for all stacks u v,
  StackBadCount(v) + slack(p0) >= StackBadCount(u).
```

So the coarsest profile does not compress the problem.  It asks for a global bad-count diameter
bound, and the failure certificate is just a pair of arbitrary stacks whose gap exceeds the single
slack allowance.

The fine-profile endpoint is formal as well.  With identity representatives and zero slack, slack
budgeting and both slack/oscillation certificates are equivalent to the original
`WorstCaseIncidenceBounded` theorem.  More generally, any injective profile with in-fiber
representatives and zero slack has the same equivalence, so fine relabelings also do not simplify
#464; they merely rename the all-stack incidence problem.

The zero-slack middle case is now explicit too.  With in-fiber representatives, zero same-profile
oscillation is equivalent to exact bad-count factorization through the selected representative:
`StackBadCount u = StackBadCount (rep (profile u))`.  See
`docs/kb/deltastar-464-zero-slack-profile-factorization-2026-06-26.md`.

## Why This Is A Different Attack

Earlier profile files formalize exact fiber maximizers.  Those are enough, but a scanner can refute
them by finding one same-profile stack that beats the representative by one.

The slack route tolerates such local beaters.  A beater is fatal only if it beats the representative
by more than the declared slack.  This gives a potential middle path between:

```text
constant profile -> global maximizer problem returns;
identity or injective profile -> all-stack budget problem returns;
exact fiber maxima -> too rigid for coarse analytic profiles.
```

The formalized missing theorem is now a **fiber oscillation bound**:

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

The Lean route now factors that statement explicitly through
`ProfileFiberOscillationCertificate`, then down to `ProfileFiberSlackCertificate`.

## Next Red-Team Test

A proposed profile must now pass three checks:

```text
1. compression: #P is genuinely smaller than the stack universe;
2. oscillation: every fiber has small bad-count diameter, or every stack is within slack of rep p;
3. budget: rep p plus slack p is below the MCA budget for every used profile.
```

If (1) fails, the profile is the identity/injective route in disguise.  If (2) fails, scanners
should return a stack exceeding its allowance via
`not_profileFiberSlackDominates_iff_exists_stack_exceeds_slack`.  If (3) fails, the route is just an
above-budget representative.

There is also a coarse-profile failure mode: if the profile forgets too much, the formal endpoint
`profileFiberOscillationBounded_constant_iff_global_pairwise_bound` shows the route has become a
global pairwise diameter theorem.  That is not simpler than the original worst-stack bound unless a
new invariant explains why the diameter is small.

This does not close the floor.  It sharpens the next mathematical target from "find exact
representatives" to "prove a fiber oscillation theorem with enough slack margin."

## Follow-up: cap collapse

`docs/kb/deltastar-464-profile-slack-cap-collapse-2026-06-26.md` records the formal critique:
the slack certificate is exactly the profile-cap interface with the induced cap
`bad(rep p) + slack p`, budgeted only on used profile labels.  The slack vocabulary is useful for
scanner design, but it is not a new proof principle.
