# Delta Star production-completion gate audit (2026-08-16)

This is an independent, source-level audit of canonical issue #4 against upstream `main` at
`95b763d4f79eacbfe50d864d8d9db9715c7e68cd`. It prepares the final integration gate; it does not
claim that the production theorem, CORE, or the Proximity Prize is closed.

## Verdict

**BLOCKED on mathematical input.** The production parameterization, an unconditional two-sided
bracket, and conditional exact-pin consumers are present. The two inequalities do not meet
unconditionally. In addition, the current source explicitly shows that the commonly cited BGK
sup-bound does not by itself discharge the above-Johnson incidence input consumed by the threshold
ledger. A completion claim therefore needs either:

1. a proof of the concrete all-stack predecessor count used by the rate-one-half exact-pin theorem;
   or
2. a proved route to that count (or to an equally strong `WorstCaseIncidenceBounded` statement),
   including every bridge beyond the BGK sup-bound.

Merely assuming `BGKFloor`, restating the predecessor count as a named `Prop`, or invoking the
conditional exact-pin theorem does not pass the gate.

## Audited production surface

The exact-rate-one-half consumer is
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean` (source blob
`c04342693fa913e6ffff21249defe24362a2f7d2`). It uses:

- block length `n = 2^30`;
- dimension `k = 2^29` (the code expression uses degree bound `2^29 - 1`);
- security budget `epsStar = 2^-128`;
- the certified smooth domains in `ZMod PrizeShapePrimeP30.P` and
  `ZMod PrizeShapePrimeP30Second.P`;
- the canonical threshold `MCAThresholdLedger.mcaDeltaStar`.

The current unconditional result is the same bracket for both certified fields:

```text
178956971 / 2^30 <= mcaDeltaStar <= 31 / 64.
```

The lower side is `firstPrime_rateHalf_ladder_floor` /
`secondPrime_rateHalf_ladder_floor`; the upper side is
`firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour` /
`secondPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour`. The paired declarations are
`firstPrime_rateHalf_deltaStar_bracket` and `secondPrime_rateHalf_deltaStar_bracket`.

The exact value `31/64` is currently conditional:

- `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` assumes an all-stack
  bad-scalar cap of `2^30` one Hamming rung below `31/64`;
- `secondPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` assumes the analogous
  cap of `2^31`, reflecting the second field's normalized budget.

Those hypotheses are the missing lower inequality at the quotient ceiling. They are not proved in
the audited module.

## CORE dependency audit

`Frontier/_DeltaStarDefinitive.lean` (source blob
`509e107842417b0dd7e5c8ae1682dab6b980248a`) names `BGKFloor` and proves its implication to a
`WorstCaseIncompleteSumBound`. It does not instantiate either production predecessor-count
hypothesis above.

More sharply, `Frontier/_PrizeFloorOfBGK.lean` documents and formalizes the current dependency
shape with two explicit hypotheses:

1. `WorstCaseIncompleteSumBound` (the BGK per-frequency sup-bound); and
2. `WorstCaseIncidenceBounded` (the above-Johnson all-stack incidence bound actually consumed by
   `worstCaseIncidence_pin`).

The file states that the first input alone only feeds the energy lane and loses a triangle factor
when routed toward line incidence. Its theorem `prizeFloor_of_BGK_and_incidence` carries both
hypotheses and consumes the second. Consequently, issue #4 is not accurately represented as
"waiting only for a bare BGK sup-bound" unless a new, verified BGK-to-incidence bridge lands too.
This distinction is essential for any future completion PR.

## Sponsor-formulation caveat

The audited exact-pin conclusions use `mcaDeltaStar`, which is a supremum and need not be attained.
`Frontier/_PrizeShapeGrandChallengeRefutation.lean` proves
`not_mcaPrize_firstPrimeDomain`: the current real-valued attained-maximum `mcaPrize` formulation is
false on the first certified production-shaped domain at a supported prize rate because the good
set has no largest element.

Therefore a final PR must state one of the following explicitly:

- the sponsor accepts the corrected supremum formulation `mcaDeltaStar`; or
- a repaired sponsor-equivalent predicate has been defined and proved equivalent in the production
  regime.

Calling the existing attained-maximum predicate equivalent to `mcaDeltaStar` would contradict the
landed refutation.

## Completion checklist

| Requirement | Current status | Evidence required to change status |
|---|---|---|
| Exact production parameters and ledger object | Ready | Preserve the explicit `n`, `k`, field, domain, and `epsStar` statement |
| Unconditional lower inequality | Ready only at `178956971/2^30` | Axiom-clean declaration at the proposed exact value |
| Unconditional upper inequality | Ready at `31/64` | Existing quotient-ceiling theorem, or a stronger verified ceiling |
| Both inequalities meet | **Blocked** | Discharge the all-stack predecessor cap or provide a stronger verified floor |
| CORE-to-threshold bridge | **Blocked/incomplete** | Include the above-Johnson incidence upgrade; BGK sup-bound alone is insufficient in current source |
| Sponsor-equivalent formulation | **Needs maintainer/sponsor decision** | Accept `mcaDeltaStar` or land a corrected equivalent predicate |
| Axiom audit | Prepared, not freshly executable on this host | `#print axioms` limited to `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| Full repository validation | Environment-blocked in this audit | Successful `./scripts/validate.sh` on a host with adequate free space |
| Independent semantic audit | This document | A second reviewer should re-check quantifiers and sponsor wording on the closure commit |

## Verification transcript and environment limitation

The audit first ran the mandated focused command:

```text
$ scripts/pg-iterate.sh \
    ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean
error: .../_GenericQuotientInterpolationSpread.olean ... does not exist
```

The required substrate warm-up was then attempted. A locked targeted dependency build advanced to
`8373/8398` but failed while writing six prerequisite modules with operating-system error 28:

```text
error: resource exhausted (error code: 28, no space left on device)
```

The host volume had about 116 MiB free afterward. No shared `.lake` data was deleted or mutated
outside the build command. This is an environment blocker for fresh executable evidence, not
evidence that the target declarations fail. A closure PR must rerun, at minimum:

```text
scripts/pg-warm.sh
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DeltaStarDefinitive.lean
./scripts/lake-locked.sh build \
  ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapeRateHalfBracket
./scripts/validate.sh
```

It must retain targeted `#print axioms` output for the exact production theorem and independently
verify that no open hypothesis has merely been renamed, wrapped, or inferred through an asserted
residual.

## Gate decision

Issue #4 should remain open. The integration surface is prepared and the blocker is now explicit:
the production exact pin lacks an unconditional all-stack floor at the proposed boundary, and the
current BGK sup-bound interface does not supply that incidence statement by itself. No merge or
issue closure is justified by this audit.
