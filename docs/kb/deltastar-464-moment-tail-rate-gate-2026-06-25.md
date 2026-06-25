# Issue #464: Moment Tail Rate Gate

Date: 2026-06-25.

Status: **last-mile consumer and obstruction**, not a delta-star proof.

## Inputs Checked

- Live issue #464 and the canonical dossier
  `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.
- Local PDFs:
  - ABF26, `eprint-2026-680-ABF26.pdf`, confirming the Proximity Prize / MCA / list-decoding
    target.
  - KU25, `arxiv-2505.22059-WassersteinQuantitativeEquidistributionExponentialSums.pdf`,
    confirming that the Wasserstein machinery is quantitative equidistribution rather than a
    worst-case atom-exclusion theorem.
  - Podesta--Videla, `arxiv-2310.15378-SpectralPropertiesGeneralizedPaleyGraphs.pdf`, confirming
    the generalized-Paley spectrum/Gaussian-period dictionary.
- Note: the local path `eprint-2026-782-HKK-FailureProximityGaps.pdf` is not a valid PDF in this
  checkout; `pdftotext` reports HTML/trailer errors, so I did not use it as evidence in this pass.

## Claim Tested

The current floor route repeatedly returns to the same analytic object:

```text
M(mu_n) <= C * sqrt(n * log m)
```

or equivalently a DC-subtracted Wick/moment estimate at depth `r ~ log m`.  A moment estimate is a
legitimate route, but only if the final Markov/union-bound conversion beats the finite atom count.

For a finite family of `N` nonnegative scores and a `k`-th moment average

```text
A = average_x X(x)^k,
```

the certificate proves `X(x) <= T` for every atom when

```text
N * A <= T^k.
```

If the budget is large enough to pay for a single atom at a score `S > T`, then the moment
certificate is compatible with exactly the kind of worst-case spike the floor must exclude.

## Lean Result

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentTailRateGate.lean
```

The file defines:

```lean
powMomentSum
powMomentAverage
```

for finite score functions.  The consumer theorems are:

```lean
forall_le_of_powMomentSum_le_threshold
forall_le_of_averageMoment_card_mul_le_threshold
forall_le_of_averageMoment_card_mul_lt_threshold
```

They prove the finite last-mile rule:

```text
nonnegative scores + averageMoment <= A + #atoms * A <= T^k
  => every score <= T.
```

The obstruction theorems are:

```lean
powMomentSum_single_spike
powMomentAverage_single_spike
averageMoment_budget_allows_single_spike
averageMoment_budget_allows_single_spike_of_pow_le_card_mul
```

They construct the explicit one-spike model:

```text
X(a0) = S,   X(a) = 0 otherwise,
```

with average moment exactly `S^k / #atoms`.  Therefore if

```text
S > T
S^k <= #atoms * A
```

then the moment budget allows a supremum violation.

The headline package is:

```lean
momentTailRateGate
```

It states the consumer and the one-spike obstruction side by side.

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_MomentTailRateGate.lean
```

passed.  The axiom audit shows the expected Lean foundations and no `sorryAx`.

## Critical Essay

This clarifies the correct interpretation of the moment route.

The moment method is not an inherently lossy or fake route.  It is the right route if the moment
theorem is strong at the correct depth.  The exact finite gate says the required inequality is not
just:

```text
average X^k is small.
```

It is:

```text
#atoms * average X^k < T^k
```

or, for the prize quotient, the analogue with `#atoms = m = (p - 1) / n` after the dilation/orbit
compression is justified.  This is why the depth `k = 2r` near `log m` is load-bearing.  At shallow
depth, the budget can be small in an average sense and still leave room for one bad quotient atom.

This also sharpens the role of the DC-subtracted Wick statement.  A Wick-type estimate at depth
`r ~ log m` is not just aesthetically Gaussian; it is exactly what makes

```text
m * A / T^(2r) < 1
```

possible at `T = C * sqrt(n * log m)`.  If the characteristic-p transfer only gives the same shape
up to a factor growing too quickly with `r`, the factor survives the `2r`-th root as a constant or
worse.  If the factor is not uniformly controlled, Markov cannot exclude the singleton bad atom.

The one-spike construction is deliberately abstract.  It is not claiming that the actual Gauss
period family contains a literal arbitrary spike.  It says a moment certificate alone cannot rule
one out unless its rate crosses the atom-count gate.  Any proposed moment proof must therefore
provide either:

1. the DC-subtracted Wick/high-moment bound to depth `r ~ log m` with acceptable constants;
2. a separate structural theorem showing the actual period/stack family cannot realize the
   one-spike extremal shape; or
3. a different worst-case mechanism that bypasses moments entirely.

The ABF26 target is worst-case MCA/list-decoding.  The KU25 Wasserstein direction is distributional.
The generalized-Paley dictionary identifies the period supremum as a graph spectral radius.  The
new gate is where these languages meet: distributional and moment estimates become prize-facing
only after the atom-count rate is below one possible bad representative.

## Verdict

This does not prove `mcaConjecture`, `delta*`, `WorstCaseIncidenceBounded`, BCHKS 1.12, or the
Paley/BGK inequality.

It gives a clean audit test for future moment or equidistribution attacks:

```text
compute the effective atom count N,
compute the certified average moment A at the proposed threshold T,
check whether N * A <= T^k.
```

If the answer is no, the attack has not reached worst-case scale.  If the answer is yes, the
remaining work is exactly the hard analytic theorem producing that budget for the actual
Gauss-period / incidence family.
