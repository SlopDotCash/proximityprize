# Issue #464: quotient tails need fiber constancy

Date: 2026-06-25.

Status: **quotient-to-full-score guardrail**, not a delta-star proof.

## Inputs Checked

- Live issue #464, especially the quotient/orbit-collapse faces of the floor problem.
- `_QuotientTailSupConsumer.lean`, which gives the finite one-atom quotient-tail consumer.
- The existing quotient-tail, atom-scale, and Wasserstein notes that separate distributional tails
  from worst-case frequency bounds.

## Claim Tested

The dilation-quotient route has two logically separate obligations:

1. Prove a tail/sup estimate for a quotient score `Y : Q -> R`.
2. Prove that the original score `X : alpha -> R` is controlled by the pullback of `Y`.

The existing quotient-tail files settle the finite atom bookkeeping for the first obligation.  This
artifact pins the second obligation.

## Lean Result

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuotientFiberConstancyGate.lean
```

defines:

- `FactorsThroughBy quot X Y`: exact quotient factorization, `X a = Y (quot a)`.
- `PullbackUpper quot X Y Delta`: one-sided pullback control, `X a <= Y (quot a) + Delta`.
- `FiberUpperOscillation quot X Delta`: one-sided oscillation control within quotient fibers.

It proves:

- `forall_le_of_quotientTailMass_and_factorsThroughBy`: quotient tail below one atom plus exact
  factorization gives a full-score pointwise bound.
- `forall_le_add_of_quotientTailMass_and_pullbackUpper`: quotient tail below one atom plus pullback
  control gives a full-score pointwise bound with additive loss.
- `forall_le_add_of_representative_bound_and_fiberOscillation`: representative bounds plus a
  fiber-oscillation theorem control all points in every fiber.
- `unitQuotient_tail_zero_allows_hidden_full_spike`: a one-point quotient can have zero strict tail
  while the original score has an arbitrary hidden spike, if no pullback/fiber-control hypothesis
  relates the two scores.

## Consequence for #464

This blocks a common shortcut in the I031/dilation-quotient lane:

```text
The quotient index set has size (p - 1) / n,
so a quotient tail bound is already a bound for every frequency.
```

That inference is sound only after one proves the period statistic descends to the quotient, or an
explicit upper approximation/oscillation theorem across the quotient fibers.  Without that link, the
quotient score can be perfectly bounded and still miss a spike in the full score.

This does not solve the `delta*` floor.  It narrows the admissible quotient-chaining route:

- entropy collapse `log p -> log(p/n)` is useful only for the descended/controlled statistic;
- any proposed quotient chaining proof must state its pullback or fiber-constancy theorem explicitly;
- representative-level numerics are not enough unless the fiber oscillation is also bounded at the
  prize threshold.

## What New Math Would Look Like

A complete quotient route needs a theorem of one of these forms:

```text
X(a) = Y(quot(a))
```

for the actual Gauss-period / far-line score, or at least

```text
X(a) <= Y(quot(a)) + Delta
```

with `Delta` below the remaining prize slack.  If the route uses representatives, it needs a
fiber-oscillation theorem:

```text
X(a) <= X(rep(quot(a))) + Delta.
```

Without one of these structural inputs, quotient tail control is compatible with a hidden spike in
the full frequency space.
