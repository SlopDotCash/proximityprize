# Issue #464: propagation tail gate

Date: 2026-06-25.

Status: **tail-amplification interface**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PropagationTailGate.lean
```

formalizes the only finite way a distributional tail bound can beat the one-atom obstruction.

Earlier tail gates show:

```text
tail mass < 1 / #atoms
```

is enough to prove a pointwise/worst-case exclusion.  At or above that scale, a singleton spike is
compatible with the tail budget.

The propagation gate records the possible escape hatch:

```text
one bad atom forces at least s bad atoms
```

Then a distributional estimate only needs to beat

```text
s / #atoms
```

rather than `1 / #atoms`.

## What This Changes

This reframes a class of possible vertical-tail attacks.  A proposed theorem can avoid a full
one-atom tail bound only if it proves an **anti-spike propagation mechanism**:

```text
BadPropagates R Bad s
```

meaning every bad atom has at least `s` bad neighbors under a relation `R`.

The file proves the consumer:

```lean
forall_not_of_badPropagates_badMass_bound_lt_scale
```

and the refutation APIs:

```lean
not_minimumBadTailCard_of_exists_badCount_lt
not_badPropagates_of_badNeighborhoodCount_lt
singleton_not_minimumBadTailCard_of_one_lt
```

## Critical Verdict

Distributional Sato-Tate, Wasserstein, smoothed-tail, or quotient-tail bounds do not become
worst-case bounds by repetition or by adding more tests unless there is a structural propagation
theorem.  The new burden is concrete:

```text
prove bad atoms occur in clusters of size s,
or exhibit a singleton/small-cluster spike.
```

No Gauss-period propagation theorem is proved here.  This is an interface and a falsifiability
target for future attacks.
