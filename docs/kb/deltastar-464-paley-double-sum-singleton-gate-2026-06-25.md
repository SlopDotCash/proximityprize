# Issue #464: double-sum Paley inputs need a singleton bridge

Date: 2026-06-25

Status: abstract transfer guardrail; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PaleyDoubleSumSingletonGate.lean`

## Inputs Checked

- Live issue #464 remains open on the single-period Gauss-period bound
  `M(mu_n) <= C sqrt(n log(p/n))`.
- The local Paley-spectrum reference map identifies Kim--Yip--Yoo `arxiv-2309.09124.pdf`,
  Conjecture 2.12, as a double-character-sum Paley input over two large sets `A,B`.
- Existing `_wf9B7_PrizeBGKReductionDirections.lean` already corrects the exponent nomenclature:
  ordinary BGK/Paley power saving is weaker than the near-`1/2` exponent needed for the prize.

## Result

This gate records a separate interface issue: even before exponent strength, a double-sum theorem
does not automatically become a single-period sup theorem.

The Lean file proves:

```lean
not_singletonSecondSetEligible_of_one_lt_threshold :
  1 < threshold ->
  not (SingletonSecondSetEligible threshold aCard)
```

So if a double-sum theorem requires both input sets to have size above a nontrivial threshold, it
cannot be instantiated with the singleton second set that represents one fixed worst period.

It also proves the averaging loss:

```lean
pointwise_le_card_mul_of_average_bound :
  (forall c in B, 0 <= score c) ->
  b in B ->
  AuxiliaryAverageBound score B T ->
  score b <= #B * T
```

and that this `#B` loss is sharp:

```lean
exists_average_bound_counterexample :
  b in B -> 1 < #B -> 0 < T ->
  exists score,
    nonnegative_on_B score /\
    AuxiliaryAverageBound score B T /\
    T < score b
```

The counterexample is a one-point spike of height `#B * T`.

## Consequence For #464

A KYY-style double-character-sum input can enter the #464 floor proof only after supplying an
additional bridge:

1. a deconvolution theorem turning the large-set average into a bound for each singleton period;
2. an anti-spike theorem ruling out concentration on one auxiliary point;
3. or a genuinely single-period theorem at the near-square-root scale.

Without such a bridge, replacing the singleton by a large auxiliary set either violates the size
hypothesis or pays a cardinality factor that is far too large for the prize scale.

This complements the exponent gates in `_SubgroupExpSumPSavingGate.lean` and
`_wf9B7_PrizeBGKReductionDirections.lean`: those files say known-style power saving is not enough;
this file says a large-set double-sum theorem is not even the right input type until the
singleton/deconvolution bridge is supplied.
