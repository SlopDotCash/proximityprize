# DeltaStar #464: Quadratic Vinogradov Bounds Are the Wrong System

Date: 2026-06-25

Status: abstract transfer guardrail; not a prize proof.

## Artifact

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuadraticVinogradovWrongSystemGate.lean`

## Point

Finite-field quadratic Vinogradov mean-value inputs control the simultaneous system:

```text
sum_i (x_i - y_i) = 0
sum_i (x_i^2 - y_i^2) = 0
```

The #464 period moment only asks for the linear balance.  Adding the quadratic equation gives a
smaller solution set, so a saving for the stricter system is not automatically a saving for the
linear energy that drives the period moment.

## Lean Facts

- `strict_count_le_linear_count`: the strict linear-plus-quadratic count is always at most the
  linear count.
- `linear_bound_of_quadratic_bound_and_extra_complete`: a strict-system bound transfers to the
  linear bound only when every relevant linear solution satisfies the added quadratic equation.
- `quadratic_bound_not_force_linear_bound`: a finite countermodel shows the strict-system bound can
  hold while the linear bound fails.
- `quadraticVinogradov_wrongSystem_gate`: packages the positive transfer consumer and the
  countermodel.

## Consequence

A quadratic-VMVT theorem can still be useful if paired with a real transfer theorem from the #464
linear solution set into the stricter quadratic system.  Without that extra-equation completeness,
the theorem controls a different count and does not close the period-moment floor.
