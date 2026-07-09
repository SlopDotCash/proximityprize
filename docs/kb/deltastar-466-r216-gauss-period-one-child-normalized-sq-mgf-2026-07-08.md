# δ* #466 — R216 Gauss-period one-child normalized-square MGF

R216 packages the concrete permutation fact behind the dyadic dilation child
spectra.

For `ζ ≠ 0`, multiplication by `ζ` is a permutation of frequency space
preserving

```text
nonzeroFreqs = univ.erase 0.
```

Consequently the shifted normalized-square child spectrum

```text
b ↦ ‖η_G(ζ * b)‖^2 / σ^2
```

is just a permuted copy of

```text
b ↦ ‖η_G(b)‖^2 / σ^2.
```

The theorem

```text
largeIndexChildQuarterMGF_shift_of_nonzeroNormalizedSqResidual
```

turns R213's one-child residual

```text
NonzeroNormalizedSqQuarterMGFResidual ψ G σ
```

into the direct shifted-child `LargeIndexChildQuarterMGFLaw` needed by the
R215 one-child dyadic consumer.

Status: deterministic bridge only.  The analytic prize socket is still the
one-child nonzero normalized-square quarter-MGF residual itself.
