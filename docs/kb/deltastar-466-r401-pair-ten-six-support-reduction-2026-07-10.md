# Issue #466 R401: pair-ten is a six-support exclusion

R401 replaces the pointwise residual `PairMultiplicityTen` by a geometric obstruction suitable for
the simultaneous-resultant lane:

```text
NoSixPairSupports G :=
  every nonzero c has at most five unordered supports {x,y} with x+y=c.
```

R395 already proves that each support has at most two ordered realizations and distinct fixed-sum
supports are pairwise disjoint. Therefore `NoSixPairSupports G` implies
`PairMultiplicityTen G`. Together with R400's six-placement cover, Lean verifies

```text
NoSixPairSupports G
PrimitiveFourBoundFortyFive G
--------------------------------
fourFiber G c <= 105 * |G|       (c != 0).
```

Failure of the first producer now yields six disjoint supports, hence up to twelve distinct roots of
unity sharing one sum. This is the precise finite simultaneous-cyclotomic configuration to exclude
or refute. The result remains fixed-depth and does not by itself move the logarithmic-depth
Paley/BGK core.

## Quartic guard is mandatory

Fermat-factor probes show that `NoSixPairSupports` is false without a field-size guard:

```text
n=4096, p=319489: pairFiber(1) = 51 ordered representations (26 supports)
n=4096, p=974849: pairFiber(1) = 39 ordered representations (20 supports)
```

Both primes are far below `n^4`. At tested factors above the quartic threshold the anomaly
disappears:

```text
n=2048, p=4659775785220018543264560743076778192897:
  pair max = 4, rep4(1)/n = 29.99755859375
n=4096, p=167988556341760475137: pairFiber(1) = pairFiber(2) = 3
n=4096, p=3560841906445833920513: pairFiber(1) = pairFiber(2) = 3
```

A full sorted census of all `4096*4097/2 = 8,390,656` unordered pairs (128-bit exact modular
arithmetic) strengthens the last two rows: for each of those two quartic-regime primes, the maximum
over **every nonzero target** is exactly two unordered supports, hence ordered multiplicity at most
four. This rules out a hidden non-diagonal six-support fiber at the first tested `n=4096` rungs.

These are probe facts, not a proof of the quartic-regime producer. Any future headline must quantify
`p > n^4` (plus primality, exact order, and subgroup realization); a field-uniform reading is
refuted.
