# Issue #464: exact ratio-degree collapse for weight-bad polynomial lines

Date: 2026-06-26.

Status: **local polynomial-line closure gate**, not a delta-star floor proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Lean Surface

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/RatioMultiplicityBridge.lean
```

Existing bridge:

```lean
ArkLib.ProximityGap.RatioMultiplicity.mult_poly_le_max
ArkLib.ProximityGap.RatioMultiplicity.badScalars_empty_of_degree
```

This pass adds:

```lean
ArkLib.ProximityGap.RatioMultiplicity.badWeight_empty_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_subset_degenerate_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_le_degenerate_card_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_card_le_one
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_le_one_of_degree_exact
```

## Content

For polynomial error coordinates

```text
e0(i) = P(dom i)
e1(i) = Q(dom i),
```

on an injective domain, `mult_poly_le_max` bounds every ratio fibre by
`max(P.natDegree, Q.natDegree)`, assuming no scalar makes `P + gamma*Q` identically zero.

The new theorem composes that degree cap with
`HighMultiplicity.badWeight_empty_of_mult_cap_exact`.  It proves that the actual low-weight
bad-scalar set is empty whenever

```text
max(deg P, deg Q)
  < #{i : Q(dom i) != 0}
    + #{i : Q(dom i) = 0 and P(dom i) != 0}
    - w.
```

So the exact zero-`Q`/nonzero-`P` correction survives all the way into the polynomial-line
degree-collapse API.

There is also a degenerate-scalar version without the global nondegeneracy hypothesis.  Under the
same exact degree inequality, every low-weight bad scalar is contained in

```text
{gamma : P + gamma*Q = 0 as a polynomial}.
```

If `Q != 0`, that degenerate set has cardinality at most one.  Thus exact degree collapse leaves
either no scalar after the `hnz` hypothesis, or at most the single constant-ratio scalar without it.

## Prize Impact

This closes the **structured polynomial error-line** case at the exact threshold.  If a future
global argument can reduce every relevant prize-radius bad pair to bounded-degree polynomial error
coordinates, this theorem supplies the local empty-set step directly.

It does **not** close the smooth-domain floor by itself.  The hard case is still the one already
isolated in the dossier: arbitrary stack coordinates or arbitrary nearby codeword-pair differences,
where no uniform low-degree ratio description has been proved.  The theorem is therefore a
consumer for a future structural reduction, not that reduction itself.

## Validation

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/RatioMultiplicityBridge.lean
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.RatioMultiplicityBridge
```

The theorem audits report only the standard Lean axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
