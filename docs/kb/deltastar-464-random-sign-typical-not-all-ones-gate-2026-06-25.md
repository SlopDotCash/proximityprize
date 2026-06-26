# Issue #464: Random-Sign Typical Bounds Do Not Control All-Ones

Date: 2026-06-25

Status: finite last-mile obstruction for random-sign and noncommutative-Khintchine routes; not a
prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RandomSignTypicalNotAllOnesGate.lean`

## Local PDFs Checked

- `/Users/shawwalters/papers/arklib/SubGaussianOperatorNorm-1812.09618.pdf`
- `/Users/shawwalters/papers/arklib/arxiv-1408.5681-RandomCosetWeights.pdf`

Sub-Gaussian operator-norm estimates and random-coset weight-distribution theorems are useful
background for typical or almost-all behavior.  They do not, by themselves, bind the deterministic
all-ones signing that represents the fixed dyadic subgroup period in #464.

## Point

Random-sign matrix tools can bound a random signing, an average over signings, or all but a small
exceptional set of signings.  The Paley/BGK period object in #464 is not a random signing.  It is a
distinguished deterministic all-ones contraction.

The Lean gate models this with a finite signing type and a score function:

```lean
GoodOn
badSignCount
AtMostBadSignCount
signAverage
singletonSpike
```

## Result

The file proves that a singleton spike at the distinguished all-ones signing is compatible with:

```lean
goodOn_erased_allows_allOnes_spike
one_exception_budget_allows_allOnes_spike
average_budget_allows_allOnes_spike
badSignCount_singletonSpike
```

So the following proof shapes are not enough by themselves:

```text
all signings except all-ones are bounded,
at most one signing is exceptional,
the average score over signings is small enough to pay for one atom.
```

Each is compatible with the all-ones signing being the unique spike above the target.

## Consequence For #464

A random-sign operator-norm theorem reaches the prize only after a separate deterministic step:

```text
control the all-ones signing directly,
or force the exceptional budget below one atom,
or prove that the all-ones signing cannot be exceptional.
```

Without that last-mile theorem, random-sign typical estimates are another average-to-worst-case
route and do not bypass the thin-subgroup sup-norm wall.
