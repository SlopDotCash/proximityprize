# Issue #464: Burgess Box-Cover Exponent Gate

Date: 2026-06-25

Status: abstract transfer/exponent guardrail; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BurgessBoxCoverExponentGate.lean`

## Point

Recent Burgess-style estimates for additive boxes or sublattices can have a useful saving on an
eligible box of volume `p^alpha`.  A direct transfer to the #464 subgroup period pays the cover
volume exponent `alpha`, while the subgroup itself has size `n = p^gamma`.

The exact exponent consumer is:

```lean
boxCover_reaches_prize_iff :
  boxCoverExponent alpha nu <= prizePExponent gamma <->
    requiredBoxCoverSaving gamma alpha <= nu
```

where `prizePExponent gamma = gamma/2` and
`requiredBoxCoverSaving gamma alpha = alpha - gamma/2`.

## Result

At the binding beta-four diagonal, `gamma = 1/4`.  If a box theorem is only eligible at volume
`alpha = 1/4 + epsilon`, then the saving needed to reach the subgroup prize scale is

```lean
requiredBoxCoverSaving_binding :
  requiredBoxCoverSaving (1/4) (1/4 + epsilon) = 1/8 + epsilon
```

The gate proves that any positive `epsilon` makes this strictly stronger than the direct subgroup
threshold `1/8`:

```lean
direct_threshold_lt_boxCover_required :
  0 < epsilon ->
  1/8 < requiredBoxCoverSaving (1/4) (1/4 + epsilon)
```

It also proves both consumer directions: savings `nu <= 1/8` still miss the prize after paying the
box-cover overhead, while savings `nu >= 1/8 + epsilon` reach the exponent target.

## Consequence For #464

Box/sublattice Burgess inputs cannot be routed into #464 by a cover argument unless their saving
pays the extra cover-volume overhead.  A usable route therefore needs either a saving of
`1/8 + epsilon` at the eligible box scale, or a measure-preserving transfer theorem that avoids the
cover-volume tax.
