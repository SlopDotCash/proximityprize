# Issue #464 loop note: stack orbit representatives are a consumer, not a proof

Date: 2026-06-25.

Status: **interface progress**, not a delta-star proof.

## What changed

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackOrbitRepresentativeReduction.lean
```

This is the stack-side analogue of the already-proven period/frequency quotient reductions
(`PeriodOrbitQuotientReduction`, `_I031OrbitQuotient`).  The frequency reductions say that a Gauss
period bound can be checked on one representative per nonzero `mu_n`-coset because the period is
constant on those cosets.

The new file states the corresponding rule for the actual prize-facing object:

```text
WorstCaseIncidenceBounded C delta B
```

That hypothesis quantifies over every `WordStack`, not over frequency cosets.  A representative set
of stacks is valid only after proving two concrete facts:

1. `StackCountInvariantRel`: the actual bad-scalar count is invariant along the proposed stack
   equivalence relation;
2. `StackRelRepresentativeCover`: every stack is related to one of the chosen representatives.

Under those hypotheses, the file proves:

```lean
worstCaseIncidenceBounded_iff_representativeStacksBounded
```

and feeds the existing delta-star pin through:

```lean
deltaStar_pin_of_representativeStacksBounded
```

## Primitive-move quotient socket

The interface now also supports generated quotient relations.  Instead of proving invariance for a
large, already-closed relation in one shot, an attack can give primitive stack moves `Step` and prove:

```lean
StackCountInvariantRel C delta Step
StackRelRepresentativeCover R (StackRelChain Step)
RepresentativeStacksBounded C delta R B
```

The new checked consumers are:

```lean
stackCountInvariantRel_chain
not_stackRelChainRepresentativeCover_iff_exists_chain_uncovered
not_chainRepresentativeCoverBudget_iff_exists_chain_uncovered_or_budget_lt
dominatingCover_of_invariantStep_chainCover
worstCaseIncidenceBounded_of_chainRepresentativeStacksBounded
worstCaseIncidenceBounded_iff_chainRepresentativeStacksBounded
not_worstCaseIncidenceBounded_iff_exists_chainRepresentative_budget_lt
deltaStar_pin_of_chainRepresentativeStacksBounded
```

This is the natural socket for a rewrite-system or normal-form attack: prove each local move
preserves `StackBadCount`, prove every stack reaches a representative by finitely many moves, and
then budget only the representatives.  It still does not prove the missing classification theorem;
it makes the exact classification obligation compositional.  The failure certificate is equally
explicit: either a stack is not connected to the representative catalogue by the generated moves, or
one of the representatives already exceeds the budget.

There is also a weaker direct target:

```lean
StackDominatingRepresentativeCover
worstCaseIncidenceBounded_iff_representativeStacksBounded_of_dominatingCover
not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_dominatingCover
deltaStar_pin_of_dominatingRepresentativeCover
not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_invariantRel_cover
```

where each stack's bad count is at most the count of some representative.  This is the exact shape
of a sparse-dominance theorem.  Under such a cover, full worst-case incidence is equivalent to
bounding the representatives, failure is exactly an above-budget representative, and the scaled
budget feeds `mcaDeltaStar` directly.  The same negative form is packaged for the named
invariant-relation cover route.

The direct domination route has also been sharpened to the same budgeted-global-max normal form as
the floor-closure contract:

```lean
RepresentativeContainsGlobalMax
RepresentativeContainsBudgetedGlobalMax
stackDominatingRepresentativeCover_iff_containsGlobalMax
worstCaseIncidenceBounded_of_representativeContainsBudgetedGlobalMax
deltaStar_pin_of_representativeContainsBudgetedGlobalMax
not_representativeContainsBudgetedGlobalMax_iff_each_member_above_or_beaten
```

This matters because a large representative catalogue does not need every entry to be budgeted once
one can identify the true maximizer inside it.  The sharp certificate is now: some listed
representative is globally worst and under budget.  Its exact refutation is also local: every listed
representative is either over budget or beaten by some stack.

The negative scanner surface is now exact:

```lean
not_stackRelRepresentativeCover_iff_exists_uncovered
not_representativeStacksBounded_iff_exists_representative_budget_lt
not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all
not_representativeCoverBudget_iff_exists_uncovered_or_budget_lt
not_dominatingCoverBudget_iff_exists_beater_or_budget_lt
```

So a proposed quotient can fail in three clean ways: a stack has no representative under `Rel`, a
listed representative is above the budget, or a stack beats every representative and refutes the
dominating-cover route.  This keeps orbit quotient claims honest at the same level as the
finite-family and stack-maximizer interfaces.  The combined scanner forms package the two local
certificate failures directly: a relation-cover plus representative-budget certificate fails
exactly by an uncovered stack or an above-budget representative, while a direct domination plus
representative-budget certificate fails exactly by a stack beating every representative or an
above-budget representative.  Count invariance remains a separate theorem, as it should.

## Follow-up: a real count-invariance generator

The file now also proves count-level invariance for the affine stack action already used by the A5
orbit probes.  The new concrete lemmas are:

```lean
stackBadCount_smul_right
stackBadCount_shift
stackBadCount_smul_both
stackBadCount_comp_perm
stackBadCount_affine_rotate
```

The composite action is:

```text
(u0, u1) |-> (a * (u0 o sigma) + b * (u1 o sigma), c * (u1 o sigma)),  a,c != 0
```

where `sigma` preserves the linear code in both directions.  Unlike the earlier A5 bundled theorem,
this is not merely a probability equality.  It proves equality of the actual finite bad-scalar
counts consumed by `WorstCaseIncidenceBounded`.

This discharges one side of the desired stack quotient theorem:

```text
count invariance along the generated affine/rotation orbits
```

The missing side is still the cover/classification statement:

```text
every relevant stack is represented, or dominated, by the proposed binder/monomial/floor family.
```

## Cardinality obstruction

A companion file now records the basic size obstruction:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackRepresentativeCoverCardinality.lean
```

It proves that if every representative has relation fiber size at most `K`, then a representative
set `R` can cover the full stack universe only if

```text
Fintype.card (WordStack A (Fin 2) iota) <= R.card * K.
```

Consequences:

```lean
no_stackRepresentativeCover_of_fiberCap
stackRepresentativeCover_forces_large_fiber
stackSingletonCover_card_le_fiber
```

So a binder-sized or monomial-sized representative list cannot be accepted on symmetry rhetoric
alone.  Its relation must have enormous fibers, or the proof must be a domination theorem rather
than a literal cover theorem.

## Why this matters

The I031 quotient collapse is real, but it is a frequency-side collapse.  It reduces

```text
sup over b in F_p^*
```

to

```text
sup over F_p^* / mu_n representatives.
```

That does not automatically reduce

```text
sup over WordStack
```

to a binder stack, a monomial stack, or a small list of adjacent-profile stacks.  The new file makes
that missing step explicit.

The floor-localization route now has three honest consumer choices:

1. prove a single dominating binder stack, then use `_FloorDominationInterface`;
2. prove a finite stack representative cover, then use `_StackOrbitRepresentativeReduction`;
3. bypass representatives and prove `WorstCaseIncidenceBounded` directly.

The first two are not free consequences of the least-prime/floor-bad story.  They are classification
or sparse-dominance theorems about all MCA stacks.

## Critical verdict

This weakens a tempting but false extrapolation:

```text
period quotient collapse + binder floor-goodness => delta-star floor
```

The corrected implication is:

```text
period quotient collapse
+ binder/floor representative bounds
+ stack count invariance
+ stack representative cover or domination
=> WorstCaseIncidenceBounded
=> delta-star lower pin
```

The newly formalized bridge proves the last two arrows.  The open mathematics is now sharply named:
find the stack relation and prove the cover/invariance theorem, or prove that no such small cover can
exist without solving the same Paley/BGK incidence problem.

## Next attack

The most concrete next attempt is to define the proposed stack relation generated by:

```text
domain dilation, code automorphisms, affine line reparametrization, and monomial-degree shifts
```

and test whether all numerically worst stacks at the known small rungs fall into the binder/adjacent
representative set.  If yes, the target becomes a real classification theorem.  If no, the floor
route has a counterexample family and should be downgraded to obstruction removal only.
