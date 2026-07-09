# Issue #466 R366: centered relation anomaly

Date: 2026-07-09

## Result

Define the weighted kernel-relation anomaly by

```text
Anom = q * shadowCollisionMass - (n^(2r) - shadowEnergy).
```

The subtracted term is the off-diagonal collision numerator expected if shadow keys were mapped
uniformly into `F_q`. R366 proves the exact decomposition

```text
centeredShadowMass = (q-1) * shadowEnergy + Anom.
```

It then proves that `DCEnergyBound` is equivalent to

```text
Anom <= q * Wick - (q-1) * shadowEnergy.
```

Both results are axiom-clean.

## Significance

This is the corrected prime-ideal lattice target. Deep prize moments contain many short kernel
vectors, so neither raw relation count nor raw collision mass can be Wick-bounded. What must be
proved is weighted equidistribution: their total return mass differs from the uniform `1/q`
baseline by at most the small budget left after the characteristic-zero shadow floor. This is
the relation-lattice form of the BGK/Paley wall, with the mandatory DC term removed exactly.
