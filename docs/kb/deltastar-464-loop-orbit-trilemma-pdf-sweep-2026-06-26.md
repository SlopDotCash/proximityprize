# Issue #464 loop note: the orbit-quotient trilemma after the PDF sweep

Date: 2026-06-26.

Status: conjecture-loop progress and exact refutation tooling, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The current off-BGK hope is not "find a nice binder stack and prove it is good."  The prize-facing
object is the universal incidence hypothesis:

```lean
OpenCoreConditionalPin.WorstCaseIncidenceBounded C delta B
```

which quantifies over every `WordStack`.  Any compressed catalogue, orbit quotient, binder list, or
floor-profile scanner must therefore prove one of two genuinely global statements:

```lean
StackRelRepresentativeCover R Rel
StackDominatingRepresentativeCover C delta R
```

together with representative budget control.  The new stack-orbit API turns this into an exact
trilemma rather than an informal warning.

## The New Tool

The stack-orbit quotient route now has exact positive and negative forms:

```lean
worstCaseIncidenceBounded_iff_representativeStacksBounded
not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_invariantRel_cover
worstCaseIncidenceBounded_iff_representativeStacksBounded_of_dominatingCover
not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_dominatingCover
```

And the proposed quotient itself has exact failure certificates:

```lean
not_stackRelRepresentativeCover_iff_exists_uncovered
not_representativeStacksBounded_iff_exists_representative_budget_lt
not_stackDominatingRepresentativeCover_iff_exists_stack_beats_all
```

So a proposed finite/orbit catalogue can fail in exactly three scanner-visible ways:

```text
1. uncovered stack: no representative under Rel;
2. above-budget representative: the catalogue contains a bad stack;
3. beating stack: some outside stack has larger bad-scalar count than every representative.
```

This is the "orbit-quotient trilemma."  It does not solve the floor.  It prevents a false proof by
making the missing global classification theorem impossible to hide.

## What The Local PDF Sweep Contributed

I searched the local PDF library for proximity-gap, Reed-Solomon, subgroup-sum, Paley, Gauss-period,
Burgess, Linnik, and arithmetic-progression inputs.  The relevant local corpus includes:

```text
docs/references/proximity-gap-paley-spectrum/BGK-gausssum-crma.pdf
docs/references/proximity-gap-paley-spectrum/HBK-jointkon.pdf
/Users/shawwalters/papers/arklib/_delta_star_frontier_2026_06_14_latest/arxiv-2003.06165-diBenedetto-SubgroupSums.pdf
/Users/shawwalters/papers/arklib/_delta_star_frontier_2026_06_14_latest/arxiv-2401.04756-Kowalski-ExponentialSumsSmallSubgroupsRevisited.pdf
/Users/shawwalters/papers/arklib/_delta_star_frontier_2026_06_14_latest/arxiv-2207.12439-KatzRojasLeon-GaussSumsIndependence.pdf
/Users/shawwalters/papers/arklib/_delta_star_gaussian_period_decorrelation_2026_06_14/arxiv-2505.22059-WassersteinQuantitativeEquidistributionExponentialSums.pdf
```

The first-page checks line up with the dossier:

- Bourgain-Chang/BGK-style estimates provide nontrivial subgroup exponential-sum bounds, but not
  square-root cancellation at `|H| = p^(1/4)`.
- Heath-Brown-Konyagin treats Gauss sums from kth powers, but the prize regime sits below the
  effective Stepanov range.
- di Benedetto-Garaev-Garcia-Gonzalez-Sanchez-Shparlinski-Trujillo proves a visible saving only for
  `|H| > p^(1/4)`; the prize lives at the boundary or below it.
- Kowalski's 2024 note is an exposition of BGK and confirms the qualitative nature of the available
  saving.
- Katz/Rojas-Leon proves equidistribution and independence relations for Gauss sums, including the
  Hasse-Davenport/conjugation/Galois relation skeleton, but this is still marginal or algebraic
  structure, not a uniform sup bound over all periods.
- Kowalski-Untrau gives quantitative Wasserstein equidistribution of exponential sums; this is a
  distributional metric, not the `L-infinity` worst-period estimate needed by the floor.

I did not find a local Thorner-Zaman or Linnik PDF under the obvious names.  For that route, the
authoritative inputs remain the in-tree TZ/Linnik interfaces and the dossier's warning: ordinary
Linnik exponent 5 is not enough for the prize-scale `n^4` cutoff.

## Attempt And Refutation

Attempt: use affine stack symmetries plus floor/binder representatives to compress the universal
stack quantifier.

What held up:

```lean
stackBadCount_smul_right
stackBadCount_shift
stackBadCount_smul_both
stackBadCount_comp_perm
stackBadCount_affine_rotate
```

These are real count invariances for the actual bad-scalar count.  They prove the invariant side of
an orbit quotient.

What failed:

The invariant side is not the cover side.  A finite binder/floor catalogue still needs either
`StackRelRepresentativeCover` or `StackDominatingRepresentativeCover`.  The new exact negative
theorems show precisely how a false quotient dies: exhibit an uncovered stack, a beating stack, or
an above-budget representative.

This criticizes the previous optimistic floor-localization essay.  Bad-prime localization can
remove one modeled obstruction, but it does not supply universal stack domination.  It can prove
"this binder predicate is good at prize primes"; it cannot by itself prove "every stack is no worse
than that binder predicate."  The latter is the MCA floor.

## New Math That Would Actually Move The Floor

The next non-larp theorem must be one of:

1. A structural normal form for worst-case stacks that proves `StackRelRepresentativeCover` for an
   explicit high-fiber relation whose classes are budget-controlled.
2. A sparse domination theorem proving `StackDominatingRepresentativeCover` for a floor/profile
   representative family.
3. A direct worst-case incidence bound, bypassing representatives.
4. A genuinely new analytic input proving the BGK/Paley `L-infinity` period bound.

Options 1 and 2 are the only apparent off-BGK route, but the trilemma makes them brutally concrete.
They are not paper citations or prime-localization statements; they are global classification
theorems about all `WordStack`s.  If such a theorem is false, the counterexample has a precise shape
and should be found by the scanner interfaces now present in Lean.

## Next Lean Target

The best next formal target is a scanner-facing theorem for any proposed floor/profile catalogue:

```text
not StackDominatingRepresentativeCover
  iff there is a stack whose bad count beats every proposed representative.
```

This is already proven at the generic representative-cover level.  The next useful specialization is
to instantiate it for the profile and refined-profile representative families, so a failed floor
catalogue produces an explicit outside stack rather than a vague "classification gap."

Until that specialization survives, the prize remains open and the correct honesty label is:

```text
interface progress; no delta-star pin.
```
