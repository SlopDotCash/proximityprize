# δ* #466 — R213 nonzero normalized-square quarter-MGF residual

R211 exposed the concrete nonprincipal dilation step for the normalized-square
spectrum

```text
X_G(b) = ‖η_G(b)‖^2 / σ^2.
```

R213 gives the remaining one-child analytic input a named `MGFBound` interface:

```text
NonzeroNormalizedSqQuarterMGFResidual ψ G σ
  := MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖^2 / σ^2) 2 (1/4).
```

The theorem

```text
prize_sq_of_nonzero_normalizedSq_quarterMGFResidual
```

composes that residual with R211 and lands the same R168/S11 prize-square
endpoint for the normalized parent spectrum.  This does not prove the
concentration estimate; it names the exact normalized-square quarter-MGF socket
that remains.
