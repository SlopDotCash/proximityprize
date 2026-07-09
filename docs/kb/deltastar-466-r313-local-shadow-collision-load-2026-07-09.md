# #466 R313: local shadow-collision load

## Result

`Frontier/_R313LocalShadowCollisionLoad.lean` localizes R312's exact wraparound mass at one
characteristic-zero shadow key.  It defines

```text
localShadowCollisionLoad(v)
  = sum of NR(w) over distinct shadows w with eval(w) = eval(v).
```

The file proves the exact identity

```text
shadowCollisionMass = sum_v NR(v) * localShadowCollisionLoad(v)
```

and the histogram conservation law

```text
sum_v NR(v) = n^r.
```

Therefore a uniform local bound

```text
localShadowCollisionLoad(v) <= K
```

implies, without Cauchy--Schwarz or a square-root loss,

```text
shadowCollisionMass <= n^r * K
```

and for an exact-order power-root set,

```text
rEnergy(powerRootSet g n,r) <= shadowEnergy(n,m,r) + n^r * K.
```

## Significance

The remaining arithmetic target is now local: bound the total multiplicity of bounded
cyclotomic shadows in one nontrivial congruence class relative to a fixed shadow.  This is
strictly more structured than bounding the total number of collisions.  Resultant,
annihilator, relation-classifier, or lattice arguments can be applied to one difference
neighborhood and then summed using the exact conservation law.

At prize depth, the required value of `K` is obtained by dividing the available
DC-subtracted Wick headroom by `n^r`.  Establishing that local cap remains open.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R313LocalShadowCollisionLoad.lean
```

passed on 2026-07-09.  The axiom audit contains no `sorryAx`.
