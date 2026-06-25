# Issue #464: quotient scaled-log tail gate

Date: 2026-06-25.

Status: **constant-form tail consumer**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuotientScaledLogTailGate.lean
```

packages the quotient exponential tail gate in the constant form used at the prize threshold.

If the quotient size is `m` and the analytic tail has rate

```text
rate = kappa * log m,
```

then the strict useful side of the atom gate is:

```text
1 + log A / log m < kappa.
```

The file proves the consumer:

```lean
pulledBack_forall_le_of_scaledLogTail
pulledBack_forall_le_of_prizeSubGaussianRate
pulledBack_forall_le_of_prizeSquaredSubGaussianTail
```

and the obstruction:

```lean
scaledLogTail_budget_allows_pulledBack_spike_of_constant_le
prizeSubGaussian_budget_allows_spike_of_constant_le
```

## Critical Consequence

For a subgaussian-looking estimate at

```text
T^2 = C^2 * n * log m,
rate = c * T^2 / V,
```

the relevant scaled constant is:

```text
kappa = c * C^2 * n / V.
```

The proof is prize-facing only if this constant beats `1 + log A / log m`.  If it does not, Lean
constructs the compatible one-quotient-atom spike.  This isolates the exact constant pressure in
any quotient-tail or Lamzouri-style route.
