# δ* #466 — dyadic raw-MGF normalization refutation (2026-07-09)

## Verdict

The historical concrete Gauss-period specialization introduced in R204--R210
has a normalization bug.  The numerical experiments test the dimensionless squared
score

```text
X_b = |η_G(b)|² / |G|,
avg_{b≠0} exp(X_b / 4) ≤ 2.
```

But `_R207NonzeroGaussPeriodDilationConsumer.lean` and
`_R209NonzeroQuarterMGFResidualConsumer.lean` ask for

```text
avg_{b≠0} exp(|η_G(b)| / 4) ≤ 2.
```

The latter is not merely stronger or open.  It is **false at prize scale**.
No prize conclusion may use `NonzeroQuarterMGFResidual ψ G` as defined in
R209.  R211 and R213 already supersede this historical socket with the
normalized-square residual; the new contribution here is the exact formal
refutation and the Haar non-contraction audit.

## Exact refutation

For every `x ≥ 0`, the second Taylor term gives

```text
exp(x/4) ≥ x²/32.
```

The landed nonzero Parseval identity is

```text
Σ_{b≠0} |η_G(b)|² = q n - n²,
n = |G|, q = |F|.
```

Therefore

```text
Σ_{b≠0} exp(|η_G(b)|/4) ≥ (qn-n²)/32.
```

If `128 ≤ n` and `2n ≤ q`, then

```text
n(q-n) ≥ 64q > 64(q-1),
```

so the last lower bound is strictly greater than `2(q-1)`.  This contradicts
the raw R209 budget.

The axiom-clean formal brick is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/
  _DyadicRawQuarterMGFRefuted.lean
```

It proves:

```text
sq_div_32_le_exp_quarter
raw_quarter_sum_secondMoment_lower
not_rawQuarterMGFBound_of_secondMoment
not_rawQuarterMGFBound_of_parseval_scale
normalized_haar_defect
normalized_parent_eighth_le_child_quarter_average
aligned_haar_mgf_no_gain
```

The Parseval theorem is kept as an explicit input in the new brick so the
brick remains checkable while the shared checkout has stale pre-4.30 ArkLib
oleans.  Instantiating it with
`GaussPeriodParsevalFloor.sum_sq_erase_zero` gives the claimed refutation of
the existing R209 definition immediately.

Validation:

```text
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DyadicRawQuarterMGFRefuted.lean
✅ OK (26s), no sorryAx
```

## Correct interface (already landed in R211/R213)

For a nonempty child subgroup `G`, the intended residual, already named
`NonzeroNormalizedSqQuarterMGFResidual` in R213, is

```lean
MGFBound nonzeroFreqs
  (fun b => ‖eta ψ G b‖ ^ 2 / σ^2)
  2 (1 / 4),
```

with `σ²=|G|` in the variance normalization used by the probes.

or, unfolded,

```text
Σ_{b≠0} exp(|η_G(b)|² / (4|G|)) ≤ 2(q-1).
```

At a disjoint dyadic step `H = G ⊎ ζG`, with `n=|G|`, the three generic
scores must be instantiated as

```text
parent_b = |η_H(b)|²       / (2n),
left_b   = |η_G(b)|²       / n,
right_b  = |η_G(ζb)|²      / n.
```

Then the existing normalized Cauchy theorem gives

```text
parent_b ≤ left_b + right_b,
```

and multiplication by `ζ` permutes nonzero frequencies, so the left and
right corrected quarter sums are equal.  This is the correct way to feed the
abstract R168/R188/R198/R200 consumers.

## Exact Haar audit

For real dyadic child periods `a,b`, the normalized identity is

```text
(a+b)²/(2n)
  = a²/n + b²/n - (a-b)²/(2n).
```

Thus the Cauchy step discards exactly the Haar-difference energy
`(a-b)²/(2n)`.  At a coherent spike `a=b`, that defect vanishes and

```text
exp((1/8) * (a+a)²/(2n))
  = exp((1/4) * a²/n).
```

So the tower step is **exactly non-contracting on aligned children**.  This
matches the R188 ancestry probes: the largest parents are same-sign aligned
merges.  A Haar, Doob, Azuma, or hypercontractive rewrite cannot prove the
quarter-MGF by second-moment conservation alone.  It still needs a theorem
showing that large aligned child pairs are rare.  That theorem is the existing
joint-tail / mixed-energy wall, not a free martingale consequence.

In particular, the dyadic filtration does not itself produce martingale
differences: multiplication of the frequency by `ζ` is a deterministic
permutation, and conditional centering/independence of the child pair is an
additional arithmetic assertion.

There is also a sharp abstract countermodel to any proof using only flat
Fourier magnitudes and dyadic band energies.  On a cyclic group of order `M`,
let

```text
f(j) = sqrt(M) * 1_{j=0}.
```

Its unitary Fourier transform has modulus `1` at every character.  Hence it
has Parseval mean square `1` and exactly the dimension-predicted energy in
every Fourier-selected dyadic martingale band.  Nevertheless its squared
score is `M` at one point and zero elsewhere, so

```text
avg_j exp(|f(j)|²/4) = (exp(M/4) + M - 1) / M,
```

which is enormous.  Gauss-period Mellin coefficients likewise have flat
nonprincipal magnitudes; their *arithmetic phases* are the extra information
that must rule out this coherent delta model.  Haar-band L² conservation alone
cannot do it.

## Impact on R168--R210

The abstract deterministic calculus remains valid.  It can consume the
corrected scores above:

- R168 and R188 (generic MGF consumers);
- R190--R203 generic tail, product, covariance, budget, and permutation
  consumers;
- `_R204PrizeTowerLargeIndex.lean` and
  `_R205PrizeTowerLargeMGFConsumer.lean`;
- `_R207PrizeTowerStepConsumer.lean` and
  `_R208PrizeTowerStepToPrize.lean`;
- `_R209DyadicCauchyNormalization.lean`,
  `_R210GaussPeriodNormalizedCauchy.lean`, and
  `_R210RawDyadicPrizeTowerStep.lean`.

The following superseded concrete raw-modulus lane does **not** instantiate
the tested quarter-MGF and cannot close the route as written:

- `_R204GaussPeriodShiftQuarterSum.lean`: its permutation equality is true,
  but it is stated for the wrong raw statistic;
- `_R205GaussPeriodShiftPrizeConsumer.lean`;
- `_R206GaussPeriodDilationPrizeConsumer.lean`;
- `_R207NonzeroGaussPeriodDilationConsumer.lean`;
- `_R209NonzeroQuarterMGFResidualConsumer.lean`;
- `_R210NonzeroBulkPlusSpikesMGFConsumer.lean`.

Their theorems are conditional implications, so Lean soundness is not at
issue.  The problem is that their load-bearing concrete hypothesis is false in
the production regime.  R211--R219 are the corrected squared-normalized
successor lane and should be used instead.

## Honest endpoint

This audit refutes a shortcut; it does not refute the corrected conjecture and
does not close the proximity prize.  On the corrected R211/R213 lane, the live
residual is still

```text
avg_{b≠0} exp(|η_G(b)|²/(4|G|)) ≤ 2
```

for the production dyadic subgroups.  Proving it requires genuine
exponential-tail control, or an aligned-child rarity theorem strong enough to
imply that control.  Finite low moments and the exact Haar/L² invariant do not
supply it.
