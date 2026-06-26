# δ* #464: the singleton-cap route, its exact scanner, and why it is not yet the floor

## Thesis

The per-codeword singleton-cap route is a useful new line-list interface, not a proof of the
proximity floor.  It replaces the all-or-nothing demand

```text
every bad scalar has a second witness
```

by a quantitative defect problem:

```text
puncturedWeight + #appearingCodewords * perCodewordSingletonCap <= 2B.
```

The new Lean scanner makes the route honest.  If support-side production, support arithmetic, and
zero-direction safety are fixed, failed production now has only three local explanations:

1. the combined arithmetic is too small;
2. the large-zero-safe line-list cap is too small;
3. a concrete appearing codeword uniquely witnesses too many singleton bad scalars.

This is progress because it creates a finite, refutable object.  It is not closure because none of
the three alternatives is currently ruled out uniformly in the prize window.

## What was formalized

The earlier singleton-defect theorem says that non-singleton bad scalars pay for two incidences,
while singleton bad scalars pay for one incidence plus one defect unit:

```lean
lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
```

The new per-codeword partition refines the defect:

```lean
singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars
```

so a route can attack `codewordSingletonWitnessScalars` one codeword at a time.  The uniform API is:

```lean
UniformLargeZeroSafeCodewordSingletonBudgeted
UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted
UniformLargeZeroSafeLineListBudgeted
UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted
```

and the exact failure/scanner surface is now:

```lean
not_uniformLargeZeroSafeCodewordSingletonBudgeted_iff_exists_card_gt
not_uniformLargeZeroSafeLineListBudgeted_iff_exists_lineAppearing_gt
exists_largeZero_safe_codewordSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_lineListSingletonRouteFailure_of_not_uniformLineBadScalarsBudgeted
```

The route is now tied to the old denominator baseline:

```lean
codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement
exists_largeZero_safe_codewordSingletonRouteSupportDivFailure_of_not_uniformLineBadScalarsBudgeted
```

So if a proposed uniform cap `S` fails, Lean can already return a large-zero safe line and one
appearing codeword with

```text
S < support(u1)/(a - #zeroAgreement(c,u0,u1)).
```

This is the right shape for a future proof attempt: the failed theorem returns a line, a codeword,
and a finite scalar set rather than an opaque negated production wrapper.

## The attempted proof idea

For a fixed appearing codeword `c`, a singleton-witness scalar `γ` is a scalar for which `c` is
heavy on the line word `u0 + γ u1`, and no other codeword is heavy at the same scalar.  If a single
`c` uniquely witnesses many scalars, then the affine pencil around `c`

```text
γ -> u0 + γ u1 - c
```

has many large zero sets whose RS interpolants are all isolated.  This smells like a rigid
one-codeword algebraic object: many `γ` should force repeated high agreement patterns, hence either
another witness or a low-degree relation among the moving-support coordinates.

If this rigidity were true with a small cap `S`, the route would prove:

```text
#badScalars <= (puncturedWeight + #appearing * S) / 2.
```

Combined with a strong enough large-zero-safe line-list bound, this would improve the old
factor-two incidence loss.

## Why it fails as a proof today

The scanner exposes the missing theorem instead of hiding it.  A failed proof can always return:

```lean
∃ c ∈ lineAppearingCodewords, S < (codewordSingletonWitnessScalars ... c).card
```

There is no current theorem bounding this set by a prize-small `S`.
The best unconditional bound currently inherited by the new route is the ordinary heavy-scalar
support denominator:

```text
#codewordSingletonWitnessScalars(c) <= support(u1)/(a - #zeroAgreement(c)).
```

That is useful as a scanner but not enough as a floor proof, because it does not use uniqueness of
the witness except through subset containment.  It is precisely the baseline a genuine overlap
theorem has to beat.

The strict unique-decoding regime is an immediate warning sign: in that regime every nonempty
witness fiber is a singleton, so the singleton defect is maximal rather than sparse.  The route can
only help beyond unique decoding, where enough overlap exists to make singleton witnesses rare.
That is exactly the hard line-list region, not an elementary side case.

The support-ratio cover work gives another warning.  Its ambient scalar-times-binomial envelope
already fails arithmetically at the prize scale; improving it requires exploiting overlap inside
the finite `(γ,T)` cover before collapsing to `|F| * choose(n, a-t)`.  The singleton-cap route is
the same phenomenon in incidence language: it asks for a structural overlap theorem saying that
many heavy scalars for one codeword cannot all be unique.

## The missing mathematics

The next real theorem would be a support-ratio multiplicity statement.  A useful form would be:

```text
If one codeword c is heavy for many scalars on a large-zero-safe line,
then many of those scalars share enough moving-support structure to force
a second codeword witness, unless the line lies in an explicitly classified
low-dimensional exceptional family.
```

That theorem must be strong enough to produce a uniform cap on
`codewordSingletonWitnessScalars`.  A weak averaged statement will not close the route: the
governing MCA law takes a supremum over stacks, so one exceptional line is enough to keep the
floor open.

The plausible algebraic handle is to stratify by exact zero-direction agreement and by the
support-ratio fibers already exposed in `LineListSupportRatioFiber.lean`.  For a fixed codeword,
each scalar `γ` has a moving-support ratio fiber.  If many `γ` are singleton witnesses, then their
large ratio fibers form a packing of the moving support.  The desired bound is not the crude
packing count; it must use RS interpolation uniqueness across overlapping fibers.

## Next formal targets

1. Define a codeword-indexed support-ratio singleton cover:

```text
{(γ,T) : γ is singleton for c, T ⊆ supportRatioFiber(c,u0,u1,γ), #T = a-t}
```

and prove the exact projection/fiber identities.

2. Prove a multiplicity lower bound: if the same codeword contributes many `(γ,T)` incidences,
then either the scalar set is small or a second witness exists.  This is the first place where a
new theorem could beat the current ambient cover.

3. If the multiplicity theorem fails, use the combined scanner to extract a counterexample shape:
a large-zero safe line and one appearing codeword with too many uniquely witnessed singleton
scalars.  That object is worth probing computationally, because it is much smaller than the full
worst-stack search.

## Verdict

The singleton-cap route is a sharpened microscope, not a solved theorem.  It converts a vague
"maybe singleton defects are sparse" hope into exact Lean obligations and exact failure witnesses.
It does not bypass the BGK/Paley wall unless it can be upgraded to a universal worst-stack
domination theorem.  The most honest next move is to formalize the codeword-indexed
support-ratio singleton cover and then try to prove or refute the overlap-multiplicity claim.
