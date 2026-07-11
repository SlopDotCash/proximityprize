# SYZ46 — the census bridge: strip per-stack bad-count ⇒ the δ* pin (2026-07-11)

Issue #466 (Proximity Prize / proximity-gap). Rate `1/2`, `n = 2³⁰`, `k = 2²⁹`,
`ε* = 2⁻¹²⁸`, first certified prize field `P = PrizeShapePrimeP30.P`,
smooth-domain code `evalCode g (2³⁰) (2²⁹ − 1)`.

File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ46CensusBridge.lean`
(axiom-clean: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`).

## What this file is

SYZ33's header names four "not-cheap" wires still needed to chain the strip theorem to a
production δ* statement at `n = 2³⁰`. SYZ46 formalizes **wire (iv)**, verbatim from that header:

> "the `MCAThresholdLedger` bridge from the count bound `#bad ≤ n − 1` to the `δ*` floor."

Nothing here is open math. It is a pure re-assembly of already-landed pieces that turns the
strip's per-stack census budget into the two-sided δ* pin, and bundles the entire conditional
chain into **one Lean statement**.

## Deliverables

1. **Task 1 — the general census bound** (`epsMCA_le_of_bad_count_le`). A `mcaBadCount`-phrased
   re-export of `ProximityGap.epsMCA_le_of_badCount_le`:
   `(∀ u, mcaBadCount C δ (u 0) (u 1) ≤ B) → epsMCA C δ ≤ B / |F|`, straight from
   `epsMCA_eq_iSup_mcaBadCount` (the worst-case-uniform-probability definition of `epsMCA`).

2. **`StripCensusBound`** — the single Lean hypothesis: the transported strip conclusion at the
   concrete code,
   `∀ u, mcaBadCount (evalCode g (2³⁰) (2²⁹−1)) (predecessorRadius (2³⁰) (31·2²⁴)) (u 0) (u 1) ≤ 2³⁰ − 1`.

3. **Two-sided pin** (`deltaStar_eq_thirtyOneSixtyFour_of_census`,
   `deltaStar_ge_thirtyOneSixtyFour_of_census`). From `StripCensusBound` the threshold is pinned:
   `mcaDeltaStar (evalCode g (2³⁰) (2²⁹−1)) ε* = 31/64`. Lower half clears the prize arithmetic
   `(2³⁰−1)/P ≤ 2³⁰/P ≤ 2⁻¹²⁸` (the `hbudget` pattern) via `le_mcaDeltaStar_of_good`; upper half is
   the unconditional quotient-spread bad witness at `31/64`
   (`firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour`, SYZ6 shape). Implemented by feeding
   `firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` (the strip's tighter
   `n−1` budget subsumes that theorem's `n` budget).

4. **The final conditional** (`deltaStar_pinned_of_strip_master_hypothesis`) — the whole chain as
   one statement (see below).

## THE conditional pin — verbatim statement

```
theorem deltaStar_pinned_of_strip_master_hypothesis
    (H : ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29))
    (transport :
      ArkLib.ProximityGap.SYZ42.StripMasterHypothesis'' (ZMod P) V (2 ^ 30) (2 ^ 29) →
        StripCensusBound) :
    mcaDeltaStar (F := ZMod P) (A := ZMod P)
        (evalCode g (2 ^ 30) (2 ^ 29 - 1))
        (ProximityGap.epsStar : ENNReal) = (31 / 64 : NNReal)
```

with `{V : Type*} [AddCommGroup V] [Module (ZMod P) V] [Module.Finite (ZMod P) V]`,
`P = ArkLib.ProximityGap.PrizeShapePrimeP30.P`, `g = ...PrizeShapePrimeP30.g`.

Proof: `deltaStar_eq_thirtyOneSixtyFour_of_census (transport H)`.

Both hypotheses are load-bearing: `transport H : StripCensusBound` feeds the pin, and `transport`
is typed to consume the master hypothesis so the provenance is explicit in the statement.

## Complete, scrupulously honest hypothesis list

`StripCensusBound` is **not proved** here; it is the transported strip conclusion, folded into one
`Prop`. Its discharge requires, verbatim (SYZ33 header items (i)–(iv); SYZ40/42/43):

- **(i) `StripMasterHypothesis''.uniformSylvester`** — `SYZ40.UniformSylvesterInjective (ZMod P) n k`.
  The sole substantive open input: SYZ38 generalized-Sylvester injectivity, characterized by SYZ39
  as a bounded-height resultant non-vanishing (BGK type / additive cancellation over `μ_n`) at
  `n = 2³⁰`. Controls only the **spread branch** (`m ≥ 4`) of the strip. The **merged branch**
  (`m ≤ 3`) is already unconditional (`SYZ40.merged_branch_unconditional`).
- **(ii)** the SYZ18 / `twist_pair_indep` disjoint-residual support control (SYZ33 lemma-1 input (a)).
- **(iii) `StripMasterHypothesis''.realizabilityCore`** — the SYZ22 `SuperadditiveUnion`
  production-ledger join, in generation language. SYZ43 (`realizabilityCore_of_mcaEvent_witnesses`)
  proves its existence residue is **auto-instantiated** by any over-budget `mcaEvent` stack via the
  G87 syndrome bridge, leaving only the union-rank lower bound `hrank`
  (`realizabilityCore_of_overBudget_stack`'s sole hypothesis) — a residual **separate** from (i).
- **(iv)** the abstract-to-concrete **transport** itself: routing SYZ40's abstract band-triple /
  union-budget strip conclusion, through the G87 `mcaEvent`→syndrome bridge, to the per-stack
  `mcaBadCount` cap at the concrete smooth-domain `evalCode`. Not formalized; it is the `transport`
  hypothesis of the capstone.

None of (i)–(iv) is asserted; SYZ46 delivers **no** unconditional δ* and **no**
conditional-on-`uniformSylvester`-alone δ*. Its gain is exactly wire (iv): the census-count ⇒
δ*-pin bridge, plus the one-statement assembly of the full conditional chain with every residual
named.

## Reused substrate (all pre-landed)

- `ProximityGap.epsMCA_le_of_badCount_le`, `epsMCA_eq_iSup_mcaBadCount` (`MCABadCount.lean`,
  `MCALowerBound.lean`).
- `MCAThresholdLedger.mcaDeltaStar`, `le_mcaDeltaStar_of_good`, `mcaDeltaStar_le_of_bad`.
- `PrizeShapeRateHalfBracket.firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count`,
  `firstPrime_rateHalf_mcaDeltaStar_le_thirtyOneSixtyFour`, `predecessorRadius`,
  `latticeBoundary_le_mcaDeltaStar_of_predecessor_good`.
- `SYZ42.StripMasterHypothesis''`, `SYZ43.realizabilityCore_of_mcaEvent_witnesses`,
  `SYZ40.merged_branch_unconditional`.
```
