# R293: collision correction is secondary; generic distinct-six is the core

Date: 2026-07-09.

## Claim

With the R292 Wick bucket closed, the exact constrained sextic expansion has the useful
three-term form

```text
E3 = W(m,q) + Gdist + Coll,
```

where:

* `W(m,q)` is explicit and `W/(m^3 q^3) -> 6`;
* `Gdist = connected_L(1,1,1)_R(1,1,1)` is the fully distinct connected bucket;
* `Coll` is the sum of all repeated-index connected strata.

Exact per-sum/collision-shape aggregation shows `Coll` is secondary on every tested cell,
while `Gdist` carries the large signed arithmetic variation.

## Exact scan

Command:

```text
python3 scripts/probes/probe_r290_constrained_sextic_average.py \
  --summary --lag-check-limit 0 \
  --cells 193:8,577:8,1489:8,1153:16,4129:16,5953:32
```

Output, normalized by `scale = m^3 q^3`:

```text
      p    n     m  beta        E3      Wick    Generic  Collision  Connected
    193    8    24  2.53    3.0190    4.3160    -1.2305    -0.0664    -1.2970
    577    8    72  3.06   13.9699    5.3968    +8.6615    -0.0883    +8.5731
   1489    8   186  3.51   12.8841    5.7614    +6.9716    +0.1511    +7.1227
   1153   16    72  2.54    5.1654    5.3966    +0.3312    -0.5624    -0.2312
   4129   16   258  3.00   18.9503    5.8273   +12.6086    +0.5144   +13.1230
   5953   32   186  2.51   10.9207    5.7613    +5.6316    -0.4722    +5.1594
```

The collision correction stays within about `0.57` normalized units here.  The generic
distinct bucket ranges from `-1.23` to `+12.61`, and is plainly the load-bearing term.

## Refined proof target

The prize-facing R23 target can now be stated as:

```text
W(m,q) + Gdist <= (C - Ccoll) m^3 q^3,
|Coll| <= Ccoll m^3 q^3.
```

The collision budget is plausible as a lower-dimensional/repeated-index estimate.  The real
new theorem must control `Gdist`, the generic distinct-six connected family on the R289
hyperplane after all Wick diagonals are deleted.

This reframes the core subconvexity statement as a signed vertical equidistribution theorem
for the generic six-point family, not a uniform complete-sum bound and not a positive-energy
diagonal argument.
