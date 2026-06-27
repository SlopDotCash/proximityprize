# Issue #464: one-spike ratio profiles force numerator degree n-1

Date: 2026-06-27.

Status: **structural obstruction**, not a delta-star floor proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Lean Surface

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/RatioProfileDegreeObstruction.lean
```

This pass adds:

```lean
ProximityGap.RatioProfileDegreeObstruction.spike_numerator_degree_ge
ProximityGap.RatioProfileDegreeObstruction.sparse_numerator_degree_ge
ProximityGap.RatioProfileDegreeObstruction.spike_profile_numerator_degree_ge
ProximityGap.RatioProfileDegreeObstruction.sparse_profile_numerator_degree_ge
ProximityGap.RatioProfileDegreeObstruction.sparse_profile_support_card_add_natDegree_ge
ProximityGap.RatioProfileDegreeObstruction.not_spike_profile_of_natDegree_lt
ProximityGap.RatioProfileDegreeObstruction.not_sparse_profile_of_natDegree_lt
ProximityGap.RatioProfileDegreeObstruction.not_sparse_profile_of_support_card_add_natDegree_lt
```

## Content

Let `dom : iota -> F` be injective.  If a numerator polynomial `P` vanishes on every domain point
except `i0`, but satisfies

```text
P(dom i0) = a * Q(dom i0),  a != 0,  Q(dom i0) != 0,
```

then `P(dom i0) != 0` while all `dom i` for `i != i0` are roots.  Root counting gives the forced
lower bound

```text
|iota| - 1 <= P.natDegree.
```

The wrapper theorem packages the same obstruction for a represented ratio profile:

```text
P(dom i) = (if i = i0 then a else 0) * Q(dom i).
```

The contrapositive form records the scanner-facing no-go: if `P.natDegree < |iota| - 1`, such a
nonzero one-spike profile cannot be represented.

The sparse-support variant replaces the single spike by a finite support `S`.  If the represented
profile is zero off `S` and is nonzero at one supported point where `Q` is nonzero, then root
counting forces

```text
|iota| - #S <= P.natDegree.
```

Equivalently, a numerator of degree `< |iota| - #S` cannot represent such a nonzero profile.
The same obstruction is now packaged in subtraction-free scanner form:

```text
|iota| <= #S + P.natDegree.
```

Thus any represented sparse profile with a nonzero point must have support plus numerator degree
covering the whole domain.  The contrapositive theorem rules out representation whenever
`#S + P.natDegree < |iota|`.

## Prize Impact

This closes a tempting shortcut in the ratio-degree lane.  The local polynomial-line collapse is
useful only after a genuine structural reduction to bounded-degree polynomial/rational lines.  An
arbitrary one-spike ratio profile already forces numerator degree `n - 1`, and sparse profiles
force degree at least the complement size; equivalently, low-degree numerator representations must
have large profile support.  Thus there is no uniform low-degree representation theorem for
arbitrary bad-scalar profiles.

The remaining issue #464 gap is unchanged: prove a real domination/reduction theorem for the actual
MCA stacks, or provide a separate global codeword-pair/list-supply bound strong enough to sum the
structured per-line incidence layer.

## Validation

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/RatioProfileDegreeObstruction.lean
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier.RatioProfileDegreeObstruction
```

The new theorem audit lines report only the standard Lean axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
