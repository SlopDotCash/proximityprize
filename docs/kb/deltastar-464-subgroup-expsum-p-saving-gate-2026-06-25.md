# Issue #464: subgroup exponential-sum `p`-saving exponent gate

Date: 2026-06-25.

Status: local PDF routing + exponent guardrail, not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SubgroupExpSumPSavingGate.lean`

## Local PDFs checked

The in-repo Paley/BGK reference folder is:

```text
docs/references/proximity-gap-paley-spectrum/
```

Poppler metadata/text extraction was run on:

- `BGK-gausssum-crma.pdf`: Bourgain--Chang finite-field Gauss-sum estimate; nontrivial estimates
  for sums `sum_x psi(x^n)` under subgroup/subfield-avoidance hypotheses.
- `subgroup-expsum-2401.04756.pdf`: Kowalski exposition of Bourgain--Glibichuk--Konyagin; theorem
  shape `sum_{x in H} e_p(ax) << |H| p^{-nu}` for `|H| >= p^gamma`.
- `subgroup-expsum-2003.06165.pdf`: di Benedetto et al.; explicit improvement near
  `|H| > p^(1/4)`, still far above the square-root target at the beta-four diagonal.
- `HBK-jointkon.pdf`: Heath-Brown--Konyagin bounds for Gauss sums from kth powers; the Weil-type
  degree factor is too large in the high-degree/thin-subgroup regime.
- `shkredov-sumsets-subgroups-Zp.pdf`: additive-combinatorics sumset coverage for subgroups,
  relevant as support for the same sum-product wall, not as a direct sup-norm closure.
- `arxiv-1809.09829.pdf`: Cayley graph eigenvalue survey, routing generalized Paley eigenvalues to
  character sums/Gaussian periods.
- `arxiv-2303.16475.pdf`: Kunisky Paley spectral pseudorandomness; nearby conjectural spectral
  pseudorandomness, not a smooth-subgroup worst-period bound.
- `arxiv-2309.09124.pdf`: shifted multiplicative subgroup structure and Paley graph conjecture
  context; useful for product/shift structure but not a proved beta-four sup bound.
- `arxiv-2310.15378.pdf`: generalized Paley graph spectra and semiprimitive cases; semiprimitive
  closed forms are already ruled out in the split prime-field prize regime.
- `chung-randomlike.pdf`: image-only/poor text extraction, retained as background on quasi-random
  graph language rather than a new analytic input.

## Lean result

The common BGK/Kowalski theorem shape is:

```text
|sum_{x in H} psi(a*x)| <= C * |H| * p^(-nu)
```

At the prize diagonal `p = n^beta`, `n = |H|`, this has `n`-exponent:

```text
1 - beta * nu
```

The prize target is `n^(1/2)` up to logarithms and constants.  The Lean gate proves:

```lean
pSaving_reaches_prize_iff :
  nExponentFromPSaving beta nu <= prizeNExponent
    <-> requiredPSaving beta <= nu
```

where `requiredPSaving beta = 1 / (2 * beta)`.

At the beta-four diagonal:

```lean
pSaving_reaches_prize_beta_four :
  nExponentFromPSaving 4 nu <= prizeNExponent <-> 1 / 8 <= nu
```

and the strict obstruction:

```lean
pSaving_misses_prize_beta_four :
  prizeNExponent < nExponentFromPSaving 4 nu <-> nu < 1 / 8
```

## Consequence for #464

The PDF literature's qualitative `p^{-nu}` saving is not enough unless the saving exponent reaches
the beta-dependent threshold.  For the binding beta-four lane, a theorem must deliver `nu >= 1/8`
before it even matches the `sqrt(n)` exponent, ignoring the additional logarithmic bookkeeping.

This is separate from `_BgkChainExponentAlgebra.lean`, which tracks the in-tree moment/energy
chain via the gain `kappa_r`.  The present file records the external theorem shape seen directly in
the local subgroup-exponential-sum PDFs.

No theorem here asserts BGK, Paley cancellation, the prize floor, or any published paper's deep
input.  It is the consumer-side exponent check for proposed imports from the local PDF corpus.
