# #466 R190: dyadic tail split/product-budget anatomy

Status: exploratory probe, not a proof.

Hypothesis under test: the dyadic parent tail should be provable by a two-channel recursion,
not by the false implication that every high parent has two large children.

Deterministic split:

```text
parent >= T and parent <= left + right
  => max(left,right) >= aT OR min(left,right) >= (1-a)T.
```

The first channel is an inherited one-child spike and must recurse down the dyadic tower. The
second channel is a balanced two-child merge and should be controlled by child-pair angle/mixed
equidistribution.

Probe:

```bash
python3 scripts/probes/probe_r190_dyadic_tail_split_budget.py
```

Expected reading:

- `parentMGF1/8` is the actual R168 target at the parent level.
- `productBudget` is the sufficient R168 tower budget
  `avg exp(left/8) exp(right/8)`.
- For each threshold `T` and split parameter `a`, `inherited` and `balanced` report what
  fraction of parent-tail cells fall in the two channels.
- `budget_tail`, `budget_inh`, `budget_bal` report the product-budget mass carried by the
  parent tail, inherited part, and balanced part.

Interpretation target: find whether a fixed `a` leaves balanced mass sparse enough to attack by
equidistribution while inherited mass is genuinely recursive. If no such `a` exists, the dyadic
tail-envelope route needs a different functional than threshold recursion.

## Run result

The split behaves exactly as R189 warned: for moderate thresholds, most parent tails are still
inherited one-child events for small `a`, and mostly balanced for large `a`. There is no magical
threshold split that alone proves the tail.

More importantly, the direct R168 product budget is stable and much stronger than needed:

```text
n=32  parentMGF1/8=1.153220 productBudget=1.326750
n=64  parentMGF1/8=1.154140 productBudget=1.330273
n=128 parentMGF1/8=1.154323 productBudget=1.331620
n=256 parentMGF1/8=1.154376 productBudget=1.332294
```

The product-budget value is converging to `4/3`, the independent real-Gaussian target
`E exp((X+Y)/8)` for `X,Y ~ chi^2_1`.  The existing Lean consumer only needs this budget to be
`≤ 2`, so the next hypothesis should attack the paired product MGF directly rather than proving a
threshold recursion.
