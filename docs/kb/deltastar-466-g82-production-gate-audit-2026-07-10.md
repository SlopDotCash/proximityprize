# G82 audit: the conditional production prize gate already exists (2026-07-10)

Issue #507 asks for the final prize-gate assembly: the production-parameter statement of the
delta* theorem through the canonical threshold ledger, land-able today only as a CONDITIONAL
end-to-end theorem `production delta* conclusion <== one clean named wall hypothesis`.

**Verdict: case A — the assembly exists in-tree; nothing new was written.** This note is the
audit of where every link lives, re-verified from tip `a42fe9e40`
(`scripts/pg-iterate.sh` recheck of the gate file: OK, 82s, axiom-clean).

## The gate, verbatim location

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapeRateHalfBracket.lean`

* Production parameters: `n = 2^30`, RS dimension `k = 2^29` (exact rate `1/2`, code
  `evalCode g (2^30) (2^29 - 1)` on the certified smooth power domain), field
  `ZMod P` with the Lucas-certified prize-shaped prime
  `P = 2^30 * (2^128 + 192) + 1` (`Frontier/_PrizeShapePrimeP30.lean`; second field
  `P2` with `floor(P2/2^128) = 2^31` in `_PrizeShapePrimeP30Second.lean`), budget
  `epsStar = 2^-128` (`GrandChallenges.lean:137`), conclusion in the canonical ledger
  threshold `mcaDeltaStar` (`MCAThresholdLedger`).

* **One-hypothesis-deep conditional pin** (the G82 gate):

  `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` —
  hypothesis: for every stack `(u0, u1)`, the literal bad-scalar count
  `#{gamma : mcaEvent (evalCode g (2^30) (2^29-1)) (predecessorRadius (2^30) (31*2^24)) u0 u1 gamma} <= 2^30`
  (radius `31/64 - 2^-30`, i.e. one Hamming rung below `31/64`);
  conclusion: `mcaDeltaStar ... epsStar = 31/64` **exactly**.
  `secondPrime_..._of_predecessor_count` is the same with budget `2^31 = 2n`.

* **Unconditional bracket** already landed around the gate:
  `firstPrime_rateHalf_deltaStar_bracket` / `secondPrime_rateHalf_deltaStar_bracket`:
  `178956971/2^30 <= deltaStar <= 31/64` (floor: RS staircase via
  `ProductionRegimeBracket`; ceiling: size-64 exact-quotient second-moment supply,
  `epsStar_lt_epsMCA_of_exact_rounded_quotient_supply`).

* **Refuted alternative hypothesis shape**:
  `firstPrime_rateHalf_not_halfPredecessor_badCount_le_length` — the same cap at the
  predecessor of `1/2` is impossible, so the `31/64` rung is the sharpest such gate this
  quotient mechanism leaves open.

Dependency chain (text diagram):

```text
hcount (open wall: n-scalar cap at radius 31/64 - 2^-30, all stacks)
  --epsMCA_le_of_badCount_le--> epsMCA(delta_prev) <= n/p <= epsStar
  --latticeBoundary_le_mcaDeltaStar_of_predecessor_good--> 31/64 <= mcaDeltaStar
  + firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour
      (<- epsStar_lt_epsMCA_of_exact_rounded_quotient_supply
       <- _GenericQuotientInterpolationSpread + _SecondMomentUniformFieldWindow,
          s=64, r=33, m=2^24, choose(64,33) supply)
  --le_antisymm--> mcaDeltaStar = 31/64          [all axiom-clean]
```

## Companion links (why no new file is warranted)

* Low-rate production pins are already **unconditional**:
  `_PrizeShapeLowRateExactPins.lean` — `firstPrime_rateSixteenth_deltaStar_eq_half`,
  `firstPrime_rateEighth_deltaStar_eq_half`;
  `secondPrime_rateSixteenth_seventeenThirtyTwo_le_deltaStar` (strict `> 1/2` pin).
* The real-valued sponsor predicate (`GrandMCAResolution` attained-maximum form) is
  **refuted** at the first certified field: `_PrizeShapeGrandChallengeRefutation.lean`.
  The faithful production object is the ledger threshold `mcaDeltaStar`; any final
  statement must be phrased through it (as the gate above is).
* The signed/line-list route also has its generic one-hypothesis consumer:
  `mcaDeltaStar_ge_of_zeroStratified_puncturedListBudget`
  (`Frontier/_R157PuncturedListBudgetConsumer.lean`, hypothesis
  `PuncturedListBudget` from `_LowProfileFiberCoupled.lean`, within-Johnson side
  discharged in `_S2PuncturedJohnsonDischarge.lean`). It is **not** instantiated at the
  production code — deliberately: it yields only a one-sided floor, strictly weaker than
  the rate-half quotient gate's exact pin, so instantiating it would add a redundant,
  weaker second gate, not a missing link.

## Honest gaps vs the sponsor formulation

1. The gate is conditional: the `hcount` hypothesis IS the open prize wall (a literal
   all-stack bad-scalar cap one rung below `31/64`); nothing here closes #507.
2. The conclusion pins `mcaDeltaStar` at `31/64`, the ceiling of the current quotient
   mechanism — a sharper mechanism could move the pin target; the sponsor asks to
   *determine* the threshold, which the unconditional bracket brackets but does not fix.
3. Quantifier shape: `hcount` is a per-stack finite count over `WordStack _ (Fin 2) _`
   (pairwise/line form), matching the ledger's `epsMCA` event, not a batched-affine
   multi-word form; the multi-word reduction lives separately in the MCA→GS reduction
   files and is not re-audited here.

Status: docs-only landing (G82, case A). No Lean changes.
