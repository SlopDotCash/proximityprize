# Issue #464: Jacobi finite-prefix turnover gate

Date: 2026-06-25.

Lean artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JacobiFinitePrefixTurnoverGate.lean`

## Verdict

The form-D Jacobi/Toda route needs a global recurrence-coefficient turnover theorem, not just
low-depth evidence.  The finite gate is:

```text
global coefficient ceiling = prefix ceiling + tail ceiling.
```

The Lean file proves the exact countermodel.  For any checked prefix `k <= K` and any larger height
`H > B`, the sequence

```text
b_k = 0 for k <= K,
b_{K+1} = H
```

satisfies the prefix bound but violates the global bound at the next coefficient.

## Consequence for delta-star

Jacobi coefficients are a useful sharper diagnostic for the Paley spectrum, but a proof of the
floor cannot stop at "the first several coefficients follow the Hermite law" or "the observed
turnover happens near log p."  It must prove that no coefficient beyond the checked prefix re-enters
above the prize-scale ceiling.

This is the same wall in form-D language: the missing input is a genuine tail/turnover theorem for
the char-p Hankel ratios, equivalent to controlling moments at the relevant depth.

## Proof status

The file is finite and axiom-clean.  It proves no analytic number theory and makes no claim that
the Gauss-period Jacobi matrix satisfies the missing tail bound.
