# Issue #464 loop note: single-dominator fantasy after the PDF sweep

Date: 2026-06-26.

Status: **attack/refutation progress**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Scope

This loop tried to turn the off-BGK floor/localization lane into a prize proof by adding the missing
global theorem around it.  The candidate theorem was deliberately strong:

```lean
StackDominates F C delta uStar
```

for a binder/floor-selected stack `uStar`.  If this held and `uStar` were budgeted, the existing
consumer

```lean
deltaStar_pin_of_stackDomination
```

would feed `mcaDeltaStar` directly.  This is the most economical possible non-BGK proof shape:
one explicit stack is the true worst stack.

## PDF Pass

I searched the local PDF inventory under `docs/` and `~/papers/arklib`: 327 PDFs.  The targeted
text/PDF passes focused on two questions:

1. does any paper give a global worst-stack / domination / representative-cover theorem?
2. does any paper supply the missing thin-subgroup `L^infinity` Gauss-period bound?

The relevant hits still fall into known buckets.

- `eccc-tr25-169.pdf` (`BCHKS25`) gives Johnson-range positive proximity gaps, negative evidence
  near/beyond Johnson, and the list-decoding prerequisite.  It does not classify worst MCA stacks
  above Johnson.
- `arxiv-2508.12548-LineInBall.pdf` improves algorithms for folded Reed-Solomon list decoding by
  pruning constant-dimensional affine subspaces.  This is algorithmic FRS structure, not a
  worst-case smooth-domain RS incidence bound for every `WordStack`.
- `arxiv-2601.07137-KoppartyNoisyCharacterValues.pdf` is a clean Stepanov/Weil-style algorithmic
  theorem for noisy character values of low-degree polynomials.  Its power is full-field Weil
  cancellation; it does not address additive sums restricted to a thin multiplicative subgroup.
- `LargeValuesMixedCharacterSums-2603.12159.pdf` studies extrema and tails for complete mixed
  character sums/Fekete polynomials.  It is about large values of a different complete-sum object,
  and is closer to evidence that maxima have logarithmic tails than to an upper bound for
  `max_b |sum_{x in mu_n} psi(b*x)|`.
- `Szabo-LowerBoundHighMomentsCharacterSums-2409.13436.pdf` gives lower bounds for high moments.
  The polarity is wrong for the floor proof: it can witness largeness, not bound the worst period.
- `Chattopadhyay-BurgessBoundsCharSums-Fpn-2602.22167.pdf` extends Burgess-style short
  multiplicative-character bounds over extensions.  The prize object is an additive character sum
  over a thin multiplicative subgroup in the prime field at the Burgess barrier.
- `Cornelissen-AsymptoticMahlerMeasureGaussianPeriods-2507.09303.pdf` and the related Gaussian
  period papers expose Mahler-measure, Linnik, and cyclic-field geometry.  They are useful for the
  algebraic-period dictionary, but height/Mahler averages are symmetric objects; they do not control
  the largest conjugate without a covering-radius or phase-location theorem.
- `arxiv-2604.06513-NatureSpectrumGeneralizedPaleyGraphs.pdf` classifies spectral phenomena of
  generalized Paley graphs, including real/integral/few-eigenvalue cases.  It sharpens the
  dictionary but does not give a uniform non-principal spectral-radius bound in the dyadic
  thin-subgroup regime.
- The least-prime search found no local Thorner-Zaman PDF with a confirmed sub-quartic least-prime
  exponent for `p == 1 mod 2^a`.  The local evidence remains the same: GRH-strength input would
  suffice for the binder obstruction; the unconditional sub-4 dyadic AP-prime input is not present.

This does not prove the literature has no useful theorem.  It does show the local library still has
no theorem whose output type is `StackDominates`, `StackDominatingRepresentativeCover`, or the
thin-subgroup Paley/BGK `L^infinity` bound.

## Invented Tool: The Single-Dominator Certificate

The new proof strategy was:

```text
floor localization -> budget one explicit uStar
single-dominator theorem -> uStar is globally worst
budget + domination -> WorstCaseIncidenceBounded
WorstCaseIncidenceBounded -> mcaDeltaStar lower pin
```

The Lean interface is intentionally unforgiving:

```lean
StackBounded F C delta uStar B
StackDominates F C delta uStar
worstCaseIncidenceBounded_iff_stackBounded_of_stackDomination
not_worstCaseIncidenceBounded_iff_budget_lt_stackBadCount_of_stackDomination
```

The positive side is real: if the domination theorem exists, the prize consumer is immediate.  The
negative side is now exact too:

```lean
not_stackDominates_iff_exists_strictly_larger
not_singleStackDominationCertificate_iff_exists_larger_or_budget_lt
not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
```

So the single-dominator certificate can fail only in two local ways:

```text
1. a beating stack exists: StackBadCount(uStar) < StackBadCount(u);
2. uStar itself is above the advertised budget.
```

This is the one-stack version of the orbit-cover trilemma.

## Attempt

I tried to read the PDF hits as candidate sources for the missing `StackDominates` theorem.

The most optimistic interpretation was:

```text
FRS affine-subspace pruning + BCHKS constrained agreement
  -> finite profile catalogue
  -> binder/floor representative dominates each profile
  -> one-stack or sparse-family domination.
```

The obstruction is that every arrow after "finite profile catalogue" is not in the papers.  BCHKS
works up to Johnson and records the list-decoding barrier beyond it.  FRS pruning exploits folded
structure and algorithmic subspace lists, while the prize lower pin is a worst-case statement over
all smooth-domain RS word stacks.  No theorem in the sweep says that every high-incidence line has
the binder/floor shape or is dominated by it.

The analytic papers similarly do not give domination.  They control complete character sums, average
moments, distributional metrics, graph spectral types, or algebraic heights.  Each becomes useful only
after an additional conversion theorem:

```text
distribution/height/moment/spectrum type -> worst non-principal period bound
```

That conversion is exactly the BGK/Paley wall.

## Refutation

The single-dominator route is not false as a logical strategy.  It is too strong to be obtained from
the currently available floor-localization inputs.

The exact refutation target is now machine-visible:

```lean
exists u, StackBadCount F C delta uStar < StackBadCount F C delta u
```

A scanner can therefore kill any proposed `uStar` by producing one outside stack with larger
bad-scalar count.  Conversely, if all known scanners fail to find such a stack, the remaining theorem
is precisely:

```lean
StackDominates F C delta uStar
```

There is no intermediate rhetorical state.  Either the selected stack dominates globally, or it does
not.  Local floor-goodness alone is silent.

## What New Math Would Actually Help

The next nonredundant theorem would be a **stack normal-form theorem**:

```text
Every worst stack has a canonical high-agreement support profile whose bad-scalar count is no larger
than a binder/floor representative.
```

It cannot be merely a finite-rung observation, a least-prime statement, or a rank-failure theorem for
one adjacent profile.  It must explain why arbitrary `WordStack`s lose no generality under the
binder/floor reduction.

Two possible formulations are worth attacking:

```lean
StackDominatingRepresentativeCover C delta R
```

for an explicit floor/profile representative family `R`, or the stronger

```lean
StackDominates F C delta uStar
```

for one selected stack.  The current Lean interfaces make both claims directly consumable and directly
refutable.

## Verdict

This loop does not close δ*.  It narrows the next off-BGK claim to an exact theorem form and gives the
scanner its falsification target.  The local PDFs do not supply the theorem.  The prize remains open:
either prove global stack domination/classification, or prove the thin-subgroup Paley/BGK sup bound.
