# #466 R371+R372 — the rotation orbit law for shadow kernel relations, machine-checked

## What landed (both axiom-clean, real locked builds)

- `Frontier/_R371ShadowKernelRotationAction.lean` (commit 51e7d825a): the shadow-evaluation
  kernel is rotation-stable — `evalVec g m (rotZ z) = g · evalVec g m z` for `g^m = −1`, and
  `rotZ` is a height-preserving bijection on nonzero integer vectors; so `z` vanishes mod `𝔭`
  iff `rotZ z` does.
- `Frontier/_R372ShadowRelationRotationEquivariance.lean` (this round): the rotation acts on
  the REALIZED side — `rotZ` is additive, `rotZ (vecOf a) = vecOf (succ a)` (the `ζ^m = −1`
  sign wrap), hence `rotZ (tupleVec t) = tupleVec (succ ∘ t)`, the char-0 histogram is
  invariant (`NR (rotZ v) = NR v`), and `rotZ` maps `keysR` into itself.

## Consequence (the r369 piece (a), now structural)

Every vanishing realized kernel relation carries its ENTIRE rotation orbit: the orbit
elements are all realized, all vanish at the same prime, and all carry identical
multiplicity/mass. This is the machine-checked mechanism behind the census's observed
excess quantization (r305: quanta 48/96; the `ζ⁵ ≡ −3` web at `p = (3¹⁶+1)/2` appearing as
a full 32-orbit) — collision mass at any prime is a sum of whole rotation-orbit
contributions, never a fraction of one.

## Status

Feeds the kernel-relation mass arc (r312–r321) and the r331 weld: any future per-orbit mass
bound multiplies by the orbit count, not the class count. The wall (bounding total collision
mass uniformly at prize depth) is unchanged. CORE OPEN, ON-BGK.
