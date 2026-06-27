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
ArkLib.ProximityGap.RatioMultiplicity.linePolynomial_ne_zero_of_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.forall_linePolynomial_ne_zero_iff_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.badWeight_empty_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badScalars_empty_of_degree_of_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.mult_poly_lt_of_degree_of_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.badWeight_empty_of_degree_exact_of_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.weightLine_card_gt_of_degree_exact_of_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.badWeight_subset_degenerate_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_subset_badWeight
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_degenerate_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_mem_iff_degenerate_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_degenerate_card_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_le_degenerate_card_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_card_le_one
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_le_one_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_eq_singleton_of
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_mem_iff
ArkLib.ProximityGap.RatioMultiplicity.degenerate_exists_iff_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_eq_singleton_of_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_mem_iff_eq_neg_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_eq_singleton_iff_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_empty_iff_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_eq_empty_or_singleton_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_card_eq_zero_iff_not_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_card_eq_one_iff_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.degenerateScalars_card_eq_if_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_singleton_of_degree_exact_of_degenerate
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_singleton_of_degree_exact_of_scalarMultiple
ArkLib.ProximityGap.RatioMultiplicity.badWeight_mem_iff_eq_neg_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_singleton_iff_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_empty_or_singleton_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_zero_or_one_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_one_iff_degenerate_exists_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_one_iff_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_empty_iff_not_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_zero_iff_not_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_card_eq_if_scalarMultiple_of_degree_exact
ArkLib.ProximityGap.RatioMultiplicity.badWeight_eq_empty_or_singleton_scalarMultiple_of_degree_exact
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

There is also a direct non-scalar-multiple front door.  Instead of supplying the per-scalar
nondegeneracy hypothesis `∀ gamma, P + gamma*Q != 0`, callers may supply the single condition
`¬ ∃ c, P = c*Q`; `forall_linePolynomial_ne_zero_iff_not_scalarMultiple` records that this is
equivalent to the needed nondegeneracy, and the front-door consumers feed both the ratio-fibre
collapse and the exact low-weight empty-set theorem.

The same front door is exposed pointwise: every scalar has multiplicity `< μ0` in the
high-multiplicity form, and every scalar line word has weight `> w` in the exact low-weight form.

There is also a degenerate-scalar version without the global nondegeneracy hypothesis.  Under the
same exact degree inequality, the low-weight bad-scalar set is exactly

```text
{gamma : P + gamma*Q = 0 as a polynomial}.
```

One direction is the degree-collapse argument; the reverse direction is automatic because a
degenerate polynomial line evaluates to the zero word and therefore has weight `0 <= w`.

If `Q != 0`, that degenerate set has cardinality at most one.  Thus exact degree collapse leaves
either no scalar after the `hnz` hypothesis, or at most the single constant-ratio scalar without it.

The singleton form is now exact: if a scalar `gamma0` satisfies `P + gamma0*Q = 0` and `Q != 0`,
then the degenerate set is exactly `{gamma0}`, and the low-weight bad-scalar set is exactly
`{gamma0}` under the same exact degree inequality.  The reverse inclusion is automatic because
`P(dom) + gamma0*Q(dom)` is the zero word, hence has weight `0 <= w`.

Equivalently, under the exact degree inequality and `Q != 0`, the structured polynomial line has a
complete dichotomy: the low-weight scalar set is either empty or exactly one singleton.  Its
cardinality is therefore exactly `0` or exactly `1`, and the count is `1` iff a degenerate scalar
`gamma0` with `P + gamma0*Q = 0` exists.

The degeneracy test is also recorded in scalar-multiple form: such a scalar exists iff
`P = c*Q` for some field scalar `c`.  Thus, under the same exact degree hypothesis and `Q != 0`,
the low-weight set is empty iff `P` is not a scalar multiple of `Q`, and has cardinality `1` iff
`P` is a scalar multiple of `Q`.

There are direct singleton consumers for this form as well: if `P = c*Q` and `Q != 0`, the
degenerate scalar set is exactly `{-c}`, and under the exact degree inequality the low-weight
bad-scalar set is exactly `{-c}`.

The singleton consumers are also bidirectional: for `Q != 0`, the degenerate scalar set is exactly
`{-c}` iff `P = c*Q`; under the exact degree inequality, the same iff holds for the low-weight
bad-scalar set.

The final set-level scalar form packages this as a direct dichotomy.  The degenerate set is empty
iff there is no scalar multiple `P = c*Q`; when `Q != 0`, it is either empty or exactly `{-c}` for
a scalar multiple.  Under the exact degree inequality, the low-weight bad-scalar set has the same
empty-or-`{-c}` scalar-multiple dichotomy.

The count-level consumers now expose the same classification without a set rewrite: the
degenerate scalar count is `0` iff there is no scalar multiple, and under the exact degree
inequality the low-weight bad-scalar count is also `0` iff there is no scalar multiple.  These
zero/empty criteria do not require `Q != 0`.  With `Q != 0`, the count is `1` iff there is a
scalar multiple and therefore equals `if exists c, P = c*Q then 1 else 0`.

The pointwise consumers expose the same classification as membership rewrites.  Under the exact
degree inequality, a scalar `gamma` is low-weight-bad iff `P + gamma*Q = 0` as a polynomial.  If
`P = c*Q` and `Q != 0`, this specializes to `gamma` being low-weight-bad iff `gamma = -c`.

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
