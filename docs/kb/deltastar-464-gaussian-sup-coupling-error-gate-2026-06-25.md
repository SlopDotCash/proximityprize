# DeltaStar #464: Gaussian Supremum Coupling Error Gate

Date: 2026-06-25

Status: abstract transfer/slack guardrail; not a prize proof.

## Artifact

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_GaussianSupCouplingErrorGate.lean`

## Local PDF Checked

- `/Users/shawwalters/papers/arklib/ChernozhukovChetverikovKato-GaussianApproxSuprema-1212.6885.pdf`

The paper is useful background for Gaussian approximation of suprema, anti-concentration, and
high-dimensional empirical-process comparison.  It is not a direct theorem about the fixed dyadic
subgroup period

```text
M(mu_n,p) = max_b |sum_{x in mu_n} e_p(b*x)|.
```

## Point

A Gaussian supremum approximation typically has an additive comparison error:

```text
actualSup <= gaussianSup + error.
```

Such a theorem proves the target `actualSup <= target` only if the Gaussian theorem lands below
`target - error`.  In normalized constants, if

```text
gaussianSup <= Cg * scale
error       <= Ce * scale
target       = Ct * scale,
```

then the last-mile condition is exactly

```text
Cg + Ce <= Ct.
```

At a sharp Gaussian extreme-value constant, there is no slack for a positive coupling error.  Thus a
CCK-style Gaussian-approximation route cannot close #464 merely by matching the Gaussian heuristic;
it must either prove a strictly sub-target Gaussian bound, prove a negligible error at the prize
scale, or supply the missing deterministic subgroup-specific input by another mechanism.

## Lean Facts

- `actual_le_target_of_gaussian_slack`: additive comparison reaches the target only with
  target-minus-error slack.
- `normalized_coupling_constant_consumer`: a normalized Gaussian constant `Cg` plus coupling
  constant `Ce` reaches target constant `Ct` under `Cg + Ce <= Ct`.
- `normalized_constant_budget_iff_error_slack`: the same condition is exactly
  `Ce <= Ct - Cg`.
- `sharp_gaussian_constant_allows_no_positive_error`: a sharp Gaussian constant cannot absorb any
  positive normalized coupling error.
- `normalized_sharp_bound_misses_with_positive_error`: at positive scale, a positive error strictly
  raises the normalized bound.

## Consequence

This does not rule out Gaussian approximation as a language for the problem.  It records the exact
slack a successful transfer would need.  For #464, the prize-facing work remains the deterministic
subgroup estimate or an approximation theorem with enough explicit slack to survive this final
constant budget.
