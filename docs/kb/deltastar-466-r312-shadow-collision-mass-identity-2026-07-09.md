# #466 R312: exact shadow collision-mass identity

## Result

`Frontier/_R312ShadowCollisionMassIdentity.lean` replaces the false-at-scale hope of full
shadow injectivity with an unconditional exact decomposition.  Define

```text
shadowCollisionMass(g,n,m,r)
  = sum over c and ordered distinct shadow keys v,w mapping to c of NR(v) NR(w).
```

For a field element `g` of exact order `n = 2m`, the file proves

```text
rEnergy(powerRootSet g n,r)
  = shadowEnergy(n,m,r) + shadowCollisionMass(g,n,m,r).
```

Consequently,

```text
shadowCollisionMass = rEnergy - shadowEnergy
```

and, for every natural headroom `B`,

```text
rEnergy <= shadowEnergy + B  iff  shadowCollisionMass <= B.
```

These are equalities/equivalences, not one-sided relaxations.  The prize-scale arithmetic
target is therefore the weighted off-diagonal collision bound on the right.  Shadow
injectivity appears only as the special case in which this mass is zero; it is no longer an
assumption in the main energy identity.

## Why this changes the target

R308 isolated the characteristic-zero shadow and R310 connected it to the general `rEnergy`
API.  Their exact-equality endpoint required injectivity of bounded shadow evaluation.
The depth-3 censuses show genuine finite-field relation webs, so that endpoint cannot be the
general prize mechanism.  R312 retains all collisions with their correct multiplicity and
identifies precisely how much energy they add.

The next direct task is to bound `shadowCollisionMass` at `r` near `log p`, ideally by the
available DC-subtracted Wick headroom.  A relation classifier can now be consumed by summing
`NR(v) NR(w)` over its collision classes; no global injectivity statement is needed.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R312ShadowCollisionMassIdentity.lean
```

passed on 2026-07-09 with no `sorryAx`; audited axioms are contained in
`{propext, Classical.choice, Quot.sound}`.
