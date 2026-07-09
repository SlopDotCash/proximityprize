# #466 R314: kernel-relation mass decomposition

## Result

`Frontier/_R314KernelRelationMassDecomposition.lean` groups R312's exact collision surplus
by difference vectors.  For a colliding pair of distinct shadow keys `(v,w)`, define

```text
d = w - v.
```

The file proves every realized `d` satisfies all three structural conditions:

```text
d != 0,
evalVec(g,d) = 0,
|d_j| <= 2r for every coordinate j.
```

Thus each contribution is a nonzero degree-`<m`, height-`<=2r` integer relation that
vanishes at the selected root modulo the field characteristic.

Defining `shadowRelationMass(d)` as the `NR(v)NR(w)` histogram autocorrelation carried by
that difference, the exact identity is

```text
shadowCollisionMass = sum_d shadowRelationMass(d),
```

where the sum is only over realized nonzero bounded kernel relations.  Consequently, if
there are at most `D` such relations and each carries mass at most `M`, then

```text
shadowCollisionMass <= D * M.
```

## Significance

This separates the prize arithmetic into two independently recognizable problems:

1. Count nonzero bounded cyclotomic relations that vanish modulo the prize prime.
2. Bound the characteristic-zero shadow-histogram autocorrelation carried by one relation.

The first is the cyclotomic norm/resultant problem; the second is a finite signed-basis
combinatorics problem.  R314 introduces no Cauchy--Schwarz or moment loss between them.

The immediate next weld is to form the integer polynomial

```text
P_d(X) = sum_{j<m} d_j X^j
```

and apply FS2/FS3: `P_d != 0`, `deg P_d < m`, and `P_d(g)=0` imply that the characteristic
divides a nonzero integer resultant with an explicit height bound.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R314KernelRelationMassDecomposition.lean
```

passed on 2026-07-09 with no `sorryAx`.
