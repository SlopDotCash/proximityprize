# The production worst-case incidence core is exactly projective

Date: 2026-07-09

## Result

`ProjectiveWorstCaseIncidence.lean` replaces the affine bad-scalar count by the intrinsic
`|F| + 1`-slot projective census from `MCAProjectiveEquivariance.lean`.  It defines

```text
ProjectiveWorstCaseIncidenceBounded C delta E :=
  forall u, badSlotCount C delta (u 0) (u 1) <= E
```

and proves, for `E < |F|`,

```text
WorstCaseIncidenceBounded C delta E
  <-> ProjectiveWorstCaseIncidenceBounded C delta E.
```

This is an exact equivalence, not an affine-to-projective estimate with an extra slot.

## Proof mechanism

The projective census decomposes as the affine bad-scalar count plus an indicator for the
infinity slot.  The easy direction drops that indicator.

For the other direction, suppose infinity is bad.  The affine hypothesis gives at most `E`
bad scalars, and `E < |F|`, so there is a good affine slot `gamma`.  Rebase the row pair by

```text
(u0, u1) |-> (u1, u0 + gamma * u1).
```

The explicit equivalence `rebaseSlotEquiv gamma : Option F ~= Option F` transports every
projective slot and moves the chosen good slot to infinity.  Therefore the projective bad
count is unchanged, while for the rebased pair it equals the entire affine count.  Applying
the universal affine hypothesis to that rebased stack proves the projective budget with no
`+1` loss.

The strict budget condition is used exactly once: to ensure a good affine slot exists.  It is
the relevant regime for normalized error thresholds below one, including the prize budget.

## Operational consumers

The module also proves

```text
epsMCA C delta <= E / |F|
  <-> ProjectiveWorstCaseIncidenceBounded C delta E
```

under the same `E < |F|` condition.  It then supplies:

- a direct projective lower-bound consumer for `mcaDeltaStar`;
- the specialization at budget `E / |F|`;
- `mcaDeltaStar_eq_of_projective_jump`, which gives an exact pin when every radius below
  `delta0` meets the projective budget and `delta0` is its first failure.

The last theorem turns a projective combinatorial jump directly into the operational
threshold, so a future incidence proof does not need to reconstruct affine probability
plumbing.

## What remains open

This result does not prove the production incidence bound.  It identifies the exact object
that must be bounded and removes a chart artifact from that task.

A concrete next route is to descend `badSlotCount` from ordered row pairs to their rank-two
projective pencil, quotienting by invertible row changes.  Rank-zero and rank-one stacks should
be split off explicitly.  On the rank-two stratum, the target becomes a worst-case incidence
bound over two-dimensional syndrome submodules rather than over arbitrary ordered generators.
The new rebase theorem proves the chart move needed for this descent; a full general-`GL2`
descent API is still to be formalized.

## Validation

The module typechecks in the stable Lean overlay.  Every exported theorem's axiom audit reports
only `propext`, `Classical.choice`, and `Quot.sound`.
