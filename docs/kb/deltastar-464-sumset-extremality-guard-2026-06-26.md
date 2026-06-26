# DeltaStar #464: sumset extremality needs a guard

Date: 2026-06-26.

Status: loop progress, not a delta-star proof.

## Thesis

`SumsetExtremalityReduction.lean` is a useful conditional reduction: if every stack is dominated by
a selected family `M`, and `M` is budgeted, then the open-core incidence budget follows.

The dangerous reading is guard-free:

```text
every stack is dominated by a monomial / selected representative
```

That form is too strong for the live #464 narrative.  Low-field, below-window, or near-line stacks
can beat the intended representative family.  A prize-useful theorem must instead say:

```text
inside a guard G, every stack is dominated by M;
outside G, a separate near/easy branch is budgeted.
```

## Lean Surface

`SumsetExtremalityGuard.lean` adds the corrected interface:

```lean
StackIncidenceBoundedOn
FamilyExtremalOn
```

The trivial-guard equivalences connect this guarded language back to the existing reduction:

```lean
familyExtremalOn_true_iff_sumsetExtremal
stackIncidenceBoundedOn_true_iff_worstCaseIncidenceBounded
```

The positive consumer is the split theorem:

```lean
worstCaseIncidenceBounded_of_split_familyExtremalOn
mcaDeltaStar_pin_of_split_familyExtremalOn
```

In words: a selected family bound plus guarded domination plus a complement bound implies the full
open-core incidence budget and hence the conditional `mcaDeltaStar` pin.

The refuter surface is:

```lean
not_stackIncidenceBoundedOn_iff_exists_counterexample
not_familyExtremalOn_iff_exists_strict_counterexample
not_worstCaseIncidenceBounded_iff_exists_counterexample
exists_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
exists_outside_counterexample_of_not_worstCaseIncidenceBounded
outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
not_familyExtremalOn_of_strict_counterexample
not_sumsetExtremal_of_strict_counterexample
not_worstCaseIncidenceBounded_of_counterexample
```

One stack that strictly beats every selected representative refutes the corresponding extremality
hypothesis.  One over-budget stack refutes the full open-core budget.

The split scanner is the main diagnostic theorem:

```lean
outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded
```

Once the selected family itself is budgeted, any full-budget failure localizes to one of two
explicit objects:

```text
outside guard:  ∃ u, ¬ G u ∧ B < incCount(u)
inside guard:   ∃ u, G u ∧ ∀ v ∈ M, incCount(v) < incCount(u)
```

A proposed guard is only viable if the outside branch is budgeted and the inside branch has no
strict representative-beater.

The finite-catalogue surface is now exposed directly for scanner outputs whose representative
family is an explicit `Finset`:

```lean
monomialIncidenceBounded_finset_coe_iff
familyExtremalOn_finset_coe_iff
stackIncidenceBoundedOn_of_finsetFamilyExtremalOn
worstCaseIncidenceBounded_of_split_finsetFamilyExtremalOn
mcaDeltaStar_pin_of_split_finsetFamilyExtremalOn
not_finsetFamilyExtremalOn_iff_exists_strict_counterexample
outside_or_guarded_strict_counterexample_of_not_worstCaseIncidenceBounded_finset
```

This is just a finite `R` specialization of the guarded API; it adds no extremality theorem.  Its
value is removing a translation step for computational certificates:

```text
finite R budgeted + guarded domination by R + outside budget
=> WorstCaseIncidenceBounded

budgeted R + failed WorstCaseIncidenceBounded
=> outside over-budget stack OR guarded stack beating every r ∈ R
```

The finite guard-cover surface generalizes this to a family of guard cells, each with its own
catalogue:

```lean
worstCaseIncidenceBounded_of_finsetGuardCover
worstCaseIncidenceBounded_of_finsetGuardCover_orOutside
mcaDeltaStar_pin_of_finsetGuardCover
mcaDeltaStar_pin_of_finsetGuardCover_orOutside
guarded_catalogue_beater_of_not_worstCaseIncidenceBounded_finsetCover
outside_or_guarded_catalogue_beater_of_not_worstCaseIncidenceBounded_finsetCover
```

This supports scanner output of the form:

```text
cover stack space by guard cells G s
budget every representative in R s
show every stack in G s is dominated by some representative in R s
=> WorstCaseIncidenceBounded

failed WorstCaseIncidenceBounded
=> specific cell s + stack beating every r ∈ R s
   OR, with an outside branch, outside over-budget stack
```

## What This Changes

This does not supply a finite-field counterexample and does not prove a windowed extremality
theorem.  It makes the proof shape honest in the current tree:

```text
selected-family budget
+ domination on a guarded branch
+ budget on the complementary branch
=> WorstCaseIncidenceBounded
=> delta-star lower pin
```

So future scanner output has a precise target.  A below-window counterexample should instantiate
`not_sumsetExtremal_of_strict_counterexample`.  A positive prize-window theorem must instantiate
`FamilyExtremalOn` for a meaningful guard and separately discharge the complement.

## Next Test

The next nonredundant step is either:

1. instantiate the strict-counterexample theorem with the small-field spike/monomial separation
   claimed in the issue thread, or
2. define the actual prize guard (`far`, large field, window interior) and prove a nontrivial
   `FamilyExtremalOn` theorem for it.

Absent one of those, an unqualified `SumsetExtremal` premise should be treated as a speculative
residual, not a usable prize hypothesis.
