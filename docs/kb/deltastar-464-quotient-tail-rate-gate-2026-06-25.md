# Issue #464: quotient tail rate gate

Date: 2026-06-25.

Status: **rate consumer**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_QuotientTailSupConsumer.lean
```

now includes the rate form of the quotient-tail gate:

```lean
quotientTailMass_lt_inv_card_of_card_mul_lt_one
pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
quotientTail_budget_allows_pulledBack_spike_of_one_le_card_mul
```

Instead of checking

```text
U < 1 / #Q,
```

future attacks can use the equivalent operational form:

```text
#Q * U < 1.
```

If a quotient score `Y : Q -> Real` has tail mass at threshold `T` bounded by `U`, and `#Q * U < 1`,
then every pulled-back full atom satisfies:

```text
Y(quot(a)) <= T.
```

Conversely, if

```text
1 <= #Q * U,
```

then a one-coset spike is still compatible with the tail budget.

## Why This Matters

This is the practical form for subgaussian, large-deviation, or Lamzouri-style arguments.

For a quotient of size

```text
#Q = m = (p - 1) / n,
```

a proposed tail estimate must satisfy:

```text
m * U_prize < 1.
```

So the missing analytic theorem is not just a pointwise-looking tail formula.  It must have enough
rate at the prize threshold that the quotient union bound is strictly below one expected bad coset.

## Critical Verdict

This sharpens the quotient entropy lead into a numerical target:

```text
prove the quotient tail at T = C * sqrt(n * log m) is < 1/m.
```

If the constants only give `m * U >= 1`, the theorem remains compatible with exactly the bad
frequency the floor must exclude.
