# Issue #464: Wasserstein Atom-Scale Barrier

Date: 2026-06-25.

Status: **negative structural progress**, not a delta-star proof.  This note records the
finite-counting obstruction faced by Wasserstein, discrepancy, and other distributional routes to
the #464 floor.

Inputs checked in this pass:

- GitHub issue #464 and the canonical dossier
  `docs/kb/deltastar-DOSSIER-v2-2026-06-22.md`.
- The existing frontier contracts for floor closure, stack/profile domination, candidate-family
  maximization, and global stack maximizers.
- Local PDF extracts for the KU25 Wasserstein/exponential-sums paper and the generalized Paley
  spectrum paper.

## Claim Tested

A natural attack is to prove that the prize-relevant frequencies, cosets, or stack representatives
are well-distributed, then consume that statement as if it ruled out every bad representative.
Wasserstein-distance bounds and effective equidistribution estimates have this shape: they control
mass seen by classes of tests or tails.

The worst-case floor is sharper.  It needs exclusion of even one bad atom, since a single surviving
frequency or stack representative can still violate the `WorstCaseIncidenceBounded` input consumed
by the conditional delta-star pin.

## Lean Result

I added:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinAtomScaleBarrier.lean
```

For a finite empirical space `α`, the file defines:

```lean
empiricalTailCount (Bad : α -> Prop)
empiricalTailMass (Bad : α -> Prop)
```

where each atom has uniform mass `1 / #α`.  The main theorem is:

```lean
atomScaleGate_for_distributional_tail_bound
```

It proves the exact gate:

```text
(every tail with mass <= U is empty)  iff  U < 1 / #α.
```

The supporting theorems prove both sides explicitly:

- any nonempty tail has mass at least one atom, `1 / #α`;
- a mass bound below `1 / #α` forces the tail to be empty;
- if `1 / #α <= U`, a singleton bad atom is compatible with the mass budget.

Validation:

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_WassersteinAtomScaleBarrier.lean
```

passed.  The axiom audit shows only the expected Lean foundations (`propext`, `Classical.choice`,
`Quot.sound`) and no `sorryAx`.

## Critique of the Route

The obstruction is not that distributional theorems are false.  The obstruction is that the prize
consumer is worst-case.

If a Wasserstein or discrepancy argument outputs a tail budget `U`, then it proves absence of all
bad representatives only after the strict inequality

```text
U < 1 / N
```

where `N` is the number of empirical atoms in the prize-relevant quotient or stack family.  In the
usual KU/prize normalization this atom count is the frequency, coset, or dilation-quotient scale,
for example the analogue of `(p - 1) / n`.  A bound that is strong on average but still much larger
than `1 / N` can coexist with a single bad representative.

Thus the attempted shortcut

```text
Wasserstein/equidistribution control
  -> small exceptional mass
  -> no bad stack representative
  -> WorstCaseIncidenceBounded
  -> delta-star floor
```

has a missing atom-scale step.  The third arrow is valid only if the exceptional-mass estimate is
below one atom.

## What Survives

The KU25 Wasserstein paper is valuable as a quantitative equidistribution source, but the pieces
checked here remain distributional.  The fixed-complexity Deligne/Katz trace-family estimates give
Wasserstein convergence for pushed-forward distributions; the ultra-short exponential-sum CLT regime
is far from the prize-scale quotient; and the logarithmic-rate discussion still controls
distributions rather than excluding every bad atom.

The generalized Paley spectrum paper gives structural information about real spectra, integrality,
and directed/undirected generalized Paley graphs.  It does not supply a new worst-eigenvalue or
worst-character-sum bound at the `sqrt(n log N)` scale needed here.

Distributional input can still be useful in two ways.

First, it can support probabilistic or average-case evidence about the stack landscape.  That is not
enough for the issue #464 floor, but it may guide a candidate classification.

Second, it can become a real worst-case input if paired with an additional theorem that upgrades
mass control to atom exclusion.  Examples would include a domination theorem for all stack fibers,
a classification showing every possible singleton spike is structurally impossible, or a
distributional bound whose scale is already below `1 / N`.

Without one of those upgrades, Wasserstein control remains a distributional certificate.  It does
not prove `mcaConjecture`, `delta*`, `WorstCaseIncidenceBounded`, BCHKS 1.12, or the Paley/BGK
core.  The floor remains open.
