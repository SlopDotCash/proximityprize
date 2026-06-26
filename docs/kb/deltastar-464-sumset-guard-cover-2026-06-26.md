# DeltaStar #464: finite guard covers for sumset extremality

Date: 2026-06-26.

Status: loop progress, not a delta-star proof.

## Thesis

The previous guarded sumset API fixed one mistake: a raw, guard-free `SumsetExtremal` premise is
too strong, because low-field, below-window, and near-line stacks can beat the intended monomial
catalogue.  The corrected single-guard shape was:

```text
inside G:  stack is dominated by a selected representative family
outside G: stack is budgeted by a separate theorem
```

That is still too rigid for a real floor proof.  A plausible prize-window proof will not have one
guard and one catalogue.  It will have a cover of stack space by several regimes:

```text
near / aligned branch
low support branch
monomial-like branch
few-component branch
structured spike branch
generic high-rank branch
```

Each branch may need its own finite representative list and its own domination theorem.  Treating
the whole cover as one catalogue hides the failure mode: a counterexample should identify the
specific branch whose representative list is too weak.

## New Lean Surface

`SumsetExtremalityGuard.lean` now has a finite guard-cover interface:

```lean
worstCaseIncidenceBounded_of_finsetGuardCover
mcaDeltaStar_pin_of_finsetGuardCover
guarded_catalogue_beater_of_not_worstCaseIncidenceBounded_finsetCover
```

and the outside-branch variant:

```lean
worstCaseIncidenceBounded_of_finsetGuardCover_orOutside
mcaDeltaStar_pin_of_finsetGuardCover_orOutside
outside_or_guarded_catalogue_beater_of_not_worstCaseIncidenceBounded_finsetCover
```

In words, for guard cells `G s` and explicit finite catalogues `R s`:

```text
guards cover all stacks
∀ s, every r ∈ R s is budgeted
∀ s, every stack in G s is dominated by some r ∈ R s
=> WorstCaseIncidenceBounded
=> conditional mcaDeltaStar pin
```

With an outside predicate `G₀`, the cover condition becomes:

```text
∀ u, G₀ u OR ∃ s, G s u
```

and one supplies a direct budget theorem for `G₀`.

## Scanner Failure Law

The main diagnostic theorem is the finite-cover failure localization:

```text
budgeted catalogues + failed WorstCaseIncidenceBounded
=> outside over-budget stack
   OR
   ∃ guard cell s and stack u ∈ G s such that
      every r ∈ R s has incCount(r) < incCount(u)
```

This is sharper than the single-guard scanner.  A failed finite cover does not merely say
"somewhere the selected family is wrong"; it returns the guard cell and the exact representative
list beaten by the counterexample.

## Critique Of The Last Attempt

The single-guard theorem was honest but still encoded a monolithic proof psychology.  It assumed a
future theorem would recognize one good predicate `G` and one representative family.  The issue
dossier says the actual landscape is not monolithic: every historical route either collapses to
the BGK/Paley wall or survives only after excluding a named exceptional class.

The finite-cover API is a better research shape.  It lets us make progress by cutting away
specific classes:

```text
prove a guard-cell domination theorem,
or get a machine-checkable beater for that cell's finite catalogue.
```

That is the right loop for the sumset route.  It neither asserts that monomials dominate
everything nor loses the ability to use monomials where they are genuinely extremal.

## Next Test

The next nonredundant step is to instantiate a two- or three-cell cover:

```text
G₀: near/aligned stacks handled by a direct easy bound;
G₁: monomial-like stacks dominated by monomial representatives;
G₂: sparse-spike stacks dominated by spike representatives or refuted by a beater.
```

If this cover fails, the new scanner theorem gives a precise object to formalize next: an
outside over-budget stack or a guard-cell beater against every listed representative.
