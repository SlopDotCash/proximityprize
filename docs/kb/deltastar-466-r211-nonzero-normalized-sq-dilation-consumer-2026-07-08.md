# δ* #466 — R211 nonzero normalized-square dilation consumer

R211 moves the concrete nonprincipal-frequency dilation route from raw norms to
the variance-normalized squared spectrum used by the numerical probes:

```text
X_G(b) = ‖η_G(b)‖^2 / σ^2.
```

Using R210's normalized Cauchy step, the parent spectrum satisfies

```text
‖η_{G∪ζG}(b)‖^2 / (2 σ^2)
  <= ‖η_G(b)‖^2 / σ^2 + ‖η_G(ζ b)‖^2 / σ^2.
```

The new Lean file is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R211NonzeroNormalizedSqDilationConsumer.lean
```

It also proves that the normalized-square quarter-MGF sum is invariant under
the nonzero multiplicative frequency shift, then feeds the existing
shifted-quarter R200/R168 prize route on `nonzeroFreqs`.

This is not the concentration theorem.  The remaining input is now the precise
nonzero one-child quarter-MGF bound for the normalized-square Gauss-period
spectrum.
