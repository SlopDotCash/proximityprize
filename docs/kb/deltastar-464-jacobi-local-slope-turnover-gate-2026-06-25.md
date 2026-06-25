# DeltaStar #464: Jacobi local-slope turnover gate

Date: 2026-06-25

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_JacobiLocalSlopeTurnoverGate.lean`
- Status: Form-D guardrail; not a delta-star proof.

## Inputs checked

- Live issue #464 remains open on the BGK/Paley wall.
- `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md` identifies Form D as the Jacobi recurrence-coefficient
  route: prove early turnover `k* = O(log p)` rather than merely inspect low-depth coefficients.
- `_JacobiFinitePrefixTurnoverGate.lean` already records that finite prefix evidence does not imply
  a global turnover ceiling.  This note covers the next natural strengthening: adding a local
  one-step slope bound.

## Result

This extends the finite-prefix Jacobi turnover guardrail to the natural next proposal:

```text
checked prefix + local one-step smoothness/Toda-step control
```

The Lean file mirrors the prefix/global-bound interface from
`_JacobiFinitePrefixTurnoverGate.lean`, then adds the new local condition `OneStepRiseBound`.

The Lean file proves the exact consumer:

```text
PrefixBound b K B
OneStepRiseBound b s      -- b(k+1) <= b(k) + s
-------------------------------------------------
b(K+t) <= B + t*s
```

So a local slope bound gives only a linearly widening envelope after the checked prefix.

The file also proves this is sharp.  For any positive slope `s > 0`, the delayed ramp

```text
b(k) = B + s * (k-K)_+
```

satisfies the prefix bound and the one-step rise bound, but violates the global ceiling `b(k) <= B`
immediately after the prefix.

## Consequence For Form D

The Jacobi/Toda route cannot close the #464 floor from:

- low-depth Hankel/recurrence evidence alone;
- local adjacent-coefficient smoothness alone;
- a Toda-step rule that permits any positive cumulative drift.

To prove the prize through Form D, the missing theorem must be one of:

- a genuine tail/turnover theorem forbidding re-entry after `K = O(log p)`;
- a zero-slope/nonincreasing theorem after the turnover point;
- a finite horizon theorem whose horizon is itself `O(log p)` and whose accumulated local drift stays
  below the prize coefficient ceiling.

This complements `_JacobiFinitePrefixTurnoverGate.lean`: prefix evidence needs a tail theorem; prefix
plus local slope needs a tail or horizon theorem as well.
