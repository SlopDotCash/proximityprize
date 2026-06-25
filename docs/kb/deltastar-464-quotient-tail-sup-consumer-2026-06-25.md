# Issue #464: quotient-tail atom gate

Date: 2026-06-25.

Status: **quotient union-bound guardrail**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuotientTailSupConsumer.lean
```

records the quotient version of the atom-scale tail consumer.

For a quotient score

```lean
Y : Q -> Real
```

and a pullback map

```lean
quot : alpha -> Q
```

Lean proves:

```lean
quotient_forall_le_of_tailMass_lt_inv_card
quotient_forall_le_of_tailMass_bound_lt_inv_card
pulledBack_forall_le_of_quotientTailMass_bound_lt_inv_card
quotientTailMass_single_spike
quotientTail_budget_allows_pulledBack_spike
atomScaleGate_for_quotientTailSupBound
```

## Critical Consequence

If a full-frequency score factors through a quotient, then the relevant atom scale is the quotient
size:

```text
U < 1 / #Q.
```

A tail estimate below that threshold gives a pointwise bound after pulling back to the full
frequency set.  At or above that threshold, Lean constructs a one-quotient-class spike, which gives
a bad full-frequency point in the preimage.

This explains the legitimate role of the dilation quotient in issue #464: it can reduce the
union-bound atom count from the full frequency set to the quotient, but it cannot remove the
one-atom requirement.  A quotient-tail proof still has to beat `1 / #Q`.
