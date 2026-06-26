# Issue #464: Tail Certificate Gate

Date: 2026-06-26.

Status: **interface/certificate progress**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Question

The distributional and EVT lanes keep returning to the same hope:

```text
tail/equidistribution control
  -> no oversized period
  -> I031 / Paley sup bound
  -> delta-star floor
```

The existing correction in `I031TailFromPointwise.lean` already says the useful I031 hypothesis is
not the gratuitously strong full tail bound at every small threshold.  It is the above-threshold
tail, and that is equivalent to the pointwise period bound at

```text
s* = sqrt(2 * C * log m).
```

This pass made the falsification side exact.

## Lean Additions

In `ArkLib/Data/CodingTheory/ProximityGap/I031SubGaussianMaxBridge.lean`:

```lean
not_SubGaussianTailBound_iff_exists_tail_count_gt
not_periodSubGaussianTailBound_iff_exists_tail_count_gt
```

These prove that the named full tail input fails if and only if there is a concrete positive
threshold `s` whose empirical tail count beats the Gaussian envelope:

```text
m * exp(-(s^2) / (2 * C)) < #{v in S : s < v}.
```

The period-specialized version is the same certificate for
`periodMagnitudes ψ G`.

In `ArkLib/Data/CodingTheory/ProximityGap/I031TailFromPointwise.lean`:

```lean
not_SubGaussianTailBoundAbove_iff_exists_gt
```

Under `0 < C` and `1 <= m`, this proves:

```text
not SubGaussianTailBoundAbove S C m
  iff
exists v in S, sqrt(2 * C * log m) < v.
```

So the corrected above-threshold tail interface has the smallest possible refutation witness: one
oversized period magnitude.

## Consequence

This separates three tasks that were easy to blur:

1. Refuting the full sub-Gaussian tail can be done by a threshold/count certificate, often at small
   `s`.  This is compatible with the probe evidence that the full tail is over-strong.
2. Refuting the above-threshold tail is exactly the same as finding one period above the
   union-bound threshold.
3. Proving the #464 floor still requires excluding that one oversized period for the prize-relevant
   thin subgroup family.

Thus a Wasserstein, discrepancy, or EVT theorem only reaches the corrected I031 consumer if it
crosses the atom-scale / worst-case gate already recorded in
`docs/kb/deltastar-464-wasserstein-atom-scale-barrier-2026-06-25.md`.

Distributional mass control can support evidence, pruning, or average-case analysis.  For the floor,
it must either produce an atom-scale exclusion theorem or directly prove the pointwise period bound.
The issue remains ON-BGK: no closure of the thin-subgroup Paley/BGK sup bound is claimed here.

## Validation

Direct ProximityGap iteration passed:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/I031SubGaussianMaxBridge.lean
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/I031TailFromPointwise.lean
```

The axiom audits for the new theorems report only the expected Lean foundations and no `sorryAx`.
