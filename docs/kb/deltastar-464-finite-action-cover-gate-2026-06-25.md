# Issue #464 loop note: finite affine orbits do not prove stack coverage

Date: 2026-06-25.

Status: **negative structural progress**, not a delta-star proof.

## Claim tested

After proving that affine stack reparametrizations preserve the actual bad-scalar count, the next
tempting move is:

```text
quotient the stack space by domain rotations, shears, and row scalings;
check a small representative family;
conclude WorstCaseIncidenceBounded.
```

The invariance part is now real.  The coverage part is not automatic.

## New formal gate

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackRepresentativeCoverCardinality.lean
```

now contains the finite-action obstruction:

```lean
StackActionRel
stackActionRel_fiber_card_le_card
stackUniverse_card_le_reps_mul_actionCard
no_stackActionRepresentativeCover_of_card_lt
stackSingletonActionCover_card_le_actionCard
not_stackActionRepresentativeCover_iff_exists_uncovered
```

For any finite transformation parameter type `G` and representative set `R`, if every stack is
covered as

```text
u = act(g, r)
```

for some `g : G` and `r : R`, then Lean proves

```text
Fintype.card (WordStack A (Fin 2) iota) <= R.card * Fintype.card G.
```

No freeness is assumed.  Collisions only make the image smaller.

The exact negative form is also formalized: finite-action coverage fails precisely when there is a
stack `u` such that

```text
forall r in R, forall g : G, act g r != u.
```

This turns a failed affine-orbit quotient into a concrete uncovered-stack search target, not just a
cardinality objection.

## Why this matters

The A5 affine/rotation action preserves count, but it is a finite action.  Therefore a small
representative family can literally cover all stacks only if

```text
#representatives * #affine-rotation-parameters >= #all stacks.
```

For the full field-valued stack space, `#all stacks` grows like `|F|^(2n)`.  The affine action has
only the parameters supplied by coordinate automorphisms plus row scalings/shears.  A binder-sized
or monomial-sized list cannot be accepted as a literal cover unless its orbit fibers are enormous
enough to pass this gate.

This does not refute a domination theorem.  It refutes a weaker but common proof slip:

```text
count invariance under a finite symmetry group
=> small representatives suffice.
```

The missing theorem must be stronger:

```text
every worst-case stack is dominated by, or classifies into, the chosen representative family.
```

That is sparse dominance/classification, not orbit quotient bookkeeping.

## Current verdict

The stack route has an honest shape:

1. count invariance under affine/rotation actions: proved;
2. finite-action cover cardinality gate: proved;
3. small binder/monomial representative coverage: still open and now visibly too strong if meant
   as literal orbit coverage;
4. domination or direct `WorstCaseIncidenceBounded`: still the prize-facing gap.

The next attack should search for a domination theorem, not a literal finite-action cover.
