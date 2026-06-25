# Issue #464 loop note: smoothing incidence only moves the wall to deconvolution

Date: 2026-06-25.

Status: **negative structural progress**, not a delta-star proof.  This note records the
smoothed-incidence/deconvolution route and why it does not bypass the current #464 open core.

## What was tested

The active API says the prize floor is not supplied by a bare Gauss-period sup bound alone.  The
operative input is the worst-case incidence / BCHKS-style hyperplane cancellation bound recorded in
`OpenCoreConditionalPin.WorstCaseIncidenceBounded` and the workbench comments.  A natural next idea
is therefore to avoid pointwise periods and instead smooth the offset-incidence profile:

```text
raw worst incidence profile  ->  smoothed profile  ->  prove smoothed bound
```

Then one tries to recover the raw worst-case profile by deconvolving the smoother.

This is genuinely different from the existing `_OnsetMollifiedSigned.lean` no-go.  That file says a
frequency multiplier cannot separate diagonal and structured off-diagonal pieces when both live on
the same defect fiber.  The route tested here is weaker and more general: even if smoothing gives a
true bound on a smoothed profile, the final recovery step has to pay its inverse norm.

## Lean result

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_IncidenceSmoothingDeconvolutionBarrier.lean
```

The main bookkeeping theorem is:

```lean
deconvolution_bound_pays_inverse_norm
```

It says that if the raw quantity is recovered from the smoothed quantity with amplification `R`,

```text
raw <= R * smooth,
```

and the smoothed theorem proves

```text
smooth <= B,
```

then the actual certified raw bound is only

```text
raw <= R * B.
```

The target-facing corollaries are:

- `target_bound_of_deconvolution_budget`: to prove `raw <= T`, the useful condition is
  `R * B <= T`, not merely `B <= T`.
- `exceeded_target_forces_inverse_loss_budget`: if a raw spike has `T < raw`, then every valid
  smoothing certificate compatible with recovery must have `T < R * B`.
- `small_multiplier_forces_inverse_product`: a Fourier multiplier of size at most `a` forces the
  inverse product `1 <= R * a` on any mode it recovers.
- `killed_mode_blocks_finite_deconvolution` and
  `killed_mode_can_pass_any_nonnegative_smooth_budget`: if the smoother kills a prize-relevant mode,
  it can pass every nonnegative smoothed budget while the raw target still fails.

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_IncidenceSmoothingDeconvolutionBarrier.lean
```

passed in 12 seconds.  The audit prints show only the expected `propext` footprint.

## Critique of the route

A smoother has two regimes.

First, if it is invertible on every prize-relevant mode, then the proof pays the inverse norm `R`.
For a low-pass or narrow smoother, `R` is the reciprocal of the smallest retained multiplier, which
is exactly where the attempted gain is spent.  A smoothed incidence bound at scale `B` is useful for
the prize only if it is stronger by this inverse factor, i.e. `B <= T / R` in ordinary normalization.

Second, if the smoother is not invertible, then it has a kernel.  A worst-case incidence spike can
live in that killed component unless a separate structural theorem rules it out.  The smoothed norm
can be zero while the raw profile is above target, so smoothing alone cannot prove a worst-case
incidence statement.

This matches the existing frontier from adjacent files:

- `_wfHJ4_EquidistDiscrepancyBlind.lean`: fixed smooth tests and discrepancy moments miss rare
  worst-case spikes.
- `_PeriodAutocovariance.lean`: autocovariance of the period field is the same period field again,
  so smoothing/correlation restates the object.
- `_ZModDFTLinftyFloor.lean`: Parseval gives the lower L-infinity floor but no upper cancellation.
- `_OnsetMollifiedSigned.lean`: frequency multipliers cannot separate diagonal from structured
  off-diagonal on a shared defect fiber.

The new file isolates the final conversion cost common to all such smoothed routes.

## What survives

The obstruction does not rule out every operator method.  It rules out a proof that says "smooth the
incidence, prove the obvious smoothed bound, and invert for free."

A live operator route would need one of:

1. a genuinely nontrivial smoother whose inverse norm is uniformly bounded while still reducing the
   worst-case incidence problem;
2. a structural theorem proving all killed modes are absent from the prize-relevant stack family;
3. a direct vector-valued hyperplane-cancellation theorem that outputs the BCHKS incidence bound
   without reconstructing the raw profile through a lossy deconvolution.

The first option looks unlikely in the abelian quotient setting already mapped by the DFT and
autocovariance files.  The second and third options are real open math, not smoothing shortcuts.
They point back to the same surviving workbench targets: direct incidence cancellation, sparse
dominance of the stack supremum, or symmetric-function coset rigidity.

No theorem here asserts `mcaConjecture`, `delta*`, `WorstCaseIncidenceBounded`, BCHKS 1.12, or the
Paley/BGK core.  The core remains open.
