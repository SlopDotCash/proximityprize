# DeltaStar #464: Full-Length Character-Sum Scale Gate

Date: 2026-06-25

Status: abstract transfer/exponent guardrail; not a prize proof.

## Artifact

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FullLengthCharacterSumScaleGate.lean`

## Local PDFs Checked

- `/Users/shawwalters/papers/arklib/LargeValuesMixedCharacterSums-2603.12159.pdf`
- `/Users/shawwalters/papers/arklib/Munsch-MaximumSizeShortCharacterSums-1805.07163.pdf`
- `/Users/shawwalters/papers/arklib/Szabo-LowerBoundHighMomentsCharacterSums-2409.13436.pdf`

These papers are useful background for large values, resonance, Fekete polynomials, interval
character sums, and high moments of Dirichlet character sums. They are not direct theorems about the
fixed dyadic subgroup period

```text
M(mu_n,p) = max_b |sum_{x in mu_n} e_p(b*x)|.
```

## Point

The natural full-length character-sum scale is `sqrt(p) = p^(1/2)` up to logarithms.  At the #464
beta-four binding diagonal, the subgroup size is

```text
n = p^(1/4),
```

so the prize target is

```text
sqrt(n) = p^(1/8)
```

up to logarithms.  Therefore any transfer from a full-length Fekete/interval/Dirichlet-character
sum theorem to the subgroup period must pay the exponent gap

```text
1/2 - 1/8 = 3/8.
```

## Lean Facts

- `transferredFullLength_reaches_prize_iff`: a transferred full-length estimate
  `p^(1/2 - nu)` reaches the subgroup prize scale exactly when
  `nu >= 1/2 - gamma/2`.
- `requiredFullLengthSaving_beta_four`: at `gamma = 1/4`, the required saving is `3/8`.
- `beta_four_misses_of_saving_lt_three_eighths`: any transfer saving below `3/8` still misses the
  subgroup exponent.
- `beta_four_reaches_of_three_eighths_le_saving`: paying `3/8` is sufficient at the exponent
  bookkeeping level.

## Consequence

Large-value lower bounds for interval or full-length character sums do not refute the expected
subgroup-period floor: they live on a different object at a much larger natural scale.  Conversely,
distributional or high-moment upper information at the full-length scale does not prove #464 unless
it is accompanied by a genuinely new transfer theorem saving `p^(3/8)` at beta four.

This is a routing guardrail, not a prize proof.  It keeps the local large-values character-sum PDFs
in the research map while preventing the common false transfer from `sqrt(p)`-scale statements to
the `sqrt(n)` subgroup target.
