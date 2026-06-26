# Issue #464 loop note: floor localization needs stack domination

Date: 2026-06-25.

Status: **interface progress**, not a delta-star proof. This note records the exact condition that
turns the off-BGK floor-localization lane into the existing prize-facing API.

## The bridge just formalized

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_FloorDominationInterface.lean
```

imports the real conditional pin from `OpenCoreConditionalPin` and repackages its incidence
hypothesis around the actual bad-scalar count:

```lean
StackBadCount F C delta u
StackBounded F C delta u B
StackDominates F C delta uStar
```

The key theorem is:

```lean
worstCaseIncidenceBounded_of_stackDomination
worstCaseIncidenceBounded_iff_stackBounded_of_stackDomination
```

It proves that a distinguished stack `uStar` can feed
`OpenCoreConditionalPin.WorstCaseIncidenceBounded` only if it dominates every other stack:

```text
forall u, StackBadCount F C delta u <= StackBadCount F C delta uStar
```

Together with a budget on `uStar`, this is sufficient for the existing delta-star lower pin via
`deltaStar_pin_of_stackDomination`.

## 2026-06-26 exact scanner surface

The interface now also has exact negative forms:

```lean
not_stackBounded_iff_budget_lt_stackBadCount
not_stackDominates_iff_exists_strictly_larger
not_singleStackDominationCertificate_iff_exists_larger_or_budget_lt
not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
not_worstCaseIncidenceBounded_iff_budget_lt_stackBadCount_of_stackDomination
```

These are small finite-order lemmas, but they matter operationally.  A proposed binder/floor
stack is not merely "unproved" as a dominator; it has a falsification predicate:

```text
exists u, StackBadCount F C delta uStar < StackBadCount F C delta u
```

The combined scanner form says the whole local certificate
`StackDominates F C delta uStar ∧ StackBounded F C delta uStar B` fails exactly by either that
larger-stack witness or by `B < StackBadCount F C delta uStar`.

Under a true domination theorem, the universal incidence hypothesis has the exact same failure
threshold as the one distinguished stack:

```text
not WorstCaseIncidenceBounded C delta B
iff B < StackBadCount F C delta uStar
```

So the floor route now exposes both sides of the contract: prove domination and one budget to feed
the prize pin, or find one larger stack to refute the proposed dominator.

## Why this matters

The previous floor-route critique was intentionally abstract: bounding one direction does not
bound a supremum over all directions. The new file pins that critique to the actual ArkLib API.

A floor-localization theorem can plausibly supply:

```text
StackBounded F C delta uStar B
```

for a binder or adjacent-profile stack selected by the bad-prime analysis. The prize API consumes:

```text
WorstCaseIncidenceBounded C delta B
```

which is extensionally the all-stack statement:

```text
forall u, StackBounded F C delta u B
```

So the missing mathematical theorem is not another local least-prime estimate. It is a domination
or reduction theorem proving that the selected floor stack is worst-case:

```text
StackDominates F C delta uStar
```

or an equivalent classification showing every maximizer reduces to the same binder family.

## Consequence for the #464 attack tree

This does not kill the floor lane. It changes its output type.

The least-prime / floor-selector program can still prove that the explicit KKH-style binder
obstruction is absent at prize-scale primes. That is a useful obstruction check and should remain in
the dossier.

But it cannot be called a delta-star proof until one of these is added:

1. a genuine stack-domination theorem for the selected floor stack;
2. a classification of all worst-case stacks into binder-equivalent forms;
3. a separate incidence theorem proving `WorstCaseIncidenceBounded` directly.

The expected hard content is (1) or (2): sparse dominance across the far-line stack space. In the
current workbench, that appears to be the same Paley/BGK incidence wall in a more structural form.

## Practical next target

Any future off-BGK floor proof should expose the following shape explicitly:

```lean
variable (uStar : WordStack A (Fin 2) iota)

-- supplied by floor localization / least-prime analysis
have hstar : StackBounded F C delta uStar B := ...

-- genuinely hard new theorem, not supplied by local floor analysis
have hdom : StackDominates F C delta uStar := ...

exact deltaStar_pin_of_stackDomination C epsilonStar hdelta hdom hstar hbudget
```

This is the honest consumer path. Everything before `hdom` is obstruction removal; `hdom` is the
missing prize-facing theorem.
