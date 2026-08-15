# Issue #466 G96: production depth four from fixed energy

Date: 2026-07-10

G96 exposes the corrected decoder's exact mapped-core count and proves the sharp production
depth-four consumer. For a finite alphabet `A` embedded injectively in an ambient additive monoid,
write `J₄` for the number of ordered equal-sum depth-four core pairs. At
`(#A,r)=(2^30,110)`, Lean kernel-checks

```text
J₄² ≤ 128 · (2^30)^13
  → #MaxCancellationCollisionSector(A,110,4) ≤ 219!! · (2^30)^110.
```

The finset-facing specialization takes `A={x // x∈G}` and the inclusion into the ambient field,
so it applies to a multiplicative subgroup alphabet without pretending that the subgroup is
additively closed.

An additional consumer factors the target through the classical fixed-depth route

```text
J₄ ≤ n⁴ E₂,
E₂² ≤ 128 n⁵.
```

The first inequality is Young/convolution transport; the second is an explicit-constant
Heath-Brown–Konyagin/Shkredov-sized additive-energy estimate. G96 proves their arithmetic
composition and the exact Wick comparison.

## Honest residual

Neither fixed-energy hypothesis is silently assumed. The in-tree `rEnergy_succ_le` is the likely
provider for `J₄ ≤ n⁴E₂` after identifying the mapped core type with subgroup `rEnergy`; the
explicit HBK estimate remains a literature/formalization input. The all-depth prize remains open.

`scripts/pg-iterate.sh` passes with standard axioms only.
