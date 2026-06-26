# DeltaStar #464: bounded-complexity pow-map critique

Date: 2026-06-26.

Status: loop progress, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The latest square-root-cancellation assault leaves one clean lesson:

```text
complete-sum lifts only help when the completing map has bounded complexity.
```

For the prize subgroup, the natural completion is the power map

```text
t |-> t^m,    m = (p - 1) / n.
```

It is exact and useful as a dictionary, but it is not a shortcut.  At prize scale `m` is the
large cofactor, so a Deligne/Weil-style complete-sum estimate pays for a high-degree map rather
than for the small subgroup alone.

## Local Paper Check

I rechecked the local PDF library around the three classical square-root-breaking templates.

- `docs/references/proximity-gap-paley-spectrum/subgroup-expsum-2401.04756.pdf` is Kowalski's
  exposition of Bourgain-Glibichuk-Konyagin.  The visible theorem gives nontrivial bounds for
  `|H| >= p^gamma`, with a saving depending on `gamma`; it is not square-root cancellation at
  `|H| = p^(1/4)`.
- `/Users/shawwalters/papers/arklib/_delta_star_frontier_2026_06_14_latest/arxiv-2003.06165-diBenedetto-SubgroupSums.pdf`
  improves explicit subgroup-sum savings for `|H| > p^(1/4)`, but the exponent is still
  `|H|^(1 - 31/2880 + o(1))`, far from `|H|^(1/2)`.
- `/Users/shawwalters/papers/arklib/PodestaVidela-SpectralGeneralizedPaleyGraphs-2310.15378.pdf`
  confirms the generalized-Paley spectrum equals Gaussian periods and gives explicit low-index /
  semiprimitive structure.  It is a dictionary and classification result, not a thin-subgroup
  spectral-radius bound.
- `/Users/shawwalters/papers/arklib/Habegger-NormOfGaussianPeriods-1611.07287.pdf` studies norms
  and Mahler-measure behavior of Gaussian periods.  Norm control is symmetric over conjugates; it
  does not bound the largest conjugate without a separate house/sup theorem.

This aligns with the issue dossier: BGK/sum-product is the real current method class, the Paley
graph dictionary names the same eigenvalue, and norm/Mahler averages do not give the missing
`L_infinity` period bound.

## Lean Surface: Power-Map Regrouping

`Frontier/PowMapFiberCard.lean` now records the finite-set core:

```lean
sum_comp_eq_nsmul_sum_of_fiber_card_eq
sum_pow_eq_nsmul_sum_image_of_fiber_card_eq
pow_fiber_card_eq_kernel_card
sum_pow_eq_kernelCard_nsmul_sum_range
pow_kernel_fiber_card_eq_gcd
sum_pow_eq_gcd_nsmul_sum_range_of_isCyclic
```

The first theorem says: if `f : s -> t` maps into `t`, every fiber over `t` has size `m`, and
`g` is a weight on `t`, then

```text
sum_{x in s} g(f x) = m * sum_{y in t} g(y).
```

The next two remove the supplied fiber hypothesis for a finite commutative group: every point in
the range of `x |-> x^e` has the same fiber size as the kernel fiber over `1`.  The cyclic
specialization identifies that multiplicity as `gcd(#G,e)`.  This is the exact combinatorial heart
of the complete power-map lift:

```text
sum_{t in F*} psi(b * t^m) = m * sum_{x in (F*)^m} psi(b * x).
```

What it proves is the equality.  What it also exposes is the obstruction: after the equality, the
left-hand side is a complete sum for the high-degree map `t^m`.  A bounded-degree Deligne estimate
does not materialize from this regrouping.

## Appearance-Filtered Replacement

The previous raw coordinate-fiber route died because it counted all interpolation completions:

```text
#coordinateAgreementFiber(S) <= |F|^(k - #S).
```

`LineListAppearanceFiber.lean` now installs the replacement object:

```lean
appearingCoordinateAgreementFiber
ZeroAppearingCoordinateFiberBudgeted
ZeroAppearingCoordinateFiberBudgetFits
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_appearingCoordinateFibers
unsafe_or_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
```

This does not prove a saving.  It changes the target to the right object:

```text
codewords in the coordinate fiber that actually appear somewhere on the affine line.
```

The raw route is backwards-compatible because raw coordinate-fiber budgets dominate
appearance-filtered budgets, but future positive work is allowed to use a smaller `M t` coming from
line appearance, ratio profiles, or support geometry.

The full line-list decomposition now consumes the appearance-filtered budget directly.  Conversely,
once the support-eligible line-list theorem, support arithmetic, and appearance-fit arithmetic are
fixed, a failed uniform bad-scalar budget must expose either zero-direction saturation or an
overfull large-zero safe appearance fiber.  If `M t >= 1` in the high range `k <= t < a`, RS
uniqueness pushes the obstruction to a low appearance fiber `t < k`.  This is the next precise
target for a positive proof or counterexample.

## Critique

The attempted route was:

```text
complete the subgroup sum -> invoke a powerful complete-sum theorem -> get square-root cancellation.
```

The missing hypothesis is bounded complexity.  The complete-sum theorem would see `t^m`, not just
the image subgroup, and `m` grows with the prize cofactor.  This is the same failure mode as the
raw coordinate-fiber route: an exact equality is true, but it forgets the structure needed for a
sharp estimate.

So the next nonredundant theorem must either:

1. prove a far-restricted appearance-fiber saving inside `LineListAppearanceFiber.lean`, or
2. prove a genuinely new thin-subgroup Paley/BGK sup bound, or
3. prove a stack/profile domination theorem that avoids the period bound entirely.

Everything else is a dictionary.

## Honest Verdict

This loop banks two useful interfaces:

- a formal complete-power-map regrouping identity;
- an appearance-filtered fiber API for the line-list route.

It does not close the core.  The floor still needs either global stack domination or the
thin-subgroup `L_infinity` Gaussian-period bound.
