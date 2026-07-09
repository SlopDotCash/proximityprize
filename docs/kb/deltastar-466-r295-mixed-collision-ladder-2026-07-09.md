# R295: mixed distinct/two-one collision is the first collision target

Date: 2026-07-09.

## Claim

The R294 repeated-index correction should be attacked in a ladder, not all at once.
The exact normalized scans show the cube-involving collision strata are negligible, while
the mixed distinct/two-one bucket can carry most of the residual collision correction.

Use the decomposition

```text
Coll = C21x21 + C111x21 + Ccube,
```

where

```text
C21x21  = connected_L(21)_R(21),
C111x21 = connected_L(111)_R(21) + connected_L(21)_R(111),
Ccube   = all strata with at least one (3) side.
```

The first nontrivial collision theorem should bound `C111x21`, a five-point constrained
family.  The `C21x21` bucket is four-point and should be easier; `Ccube` appears lower order.

## Updated exact scan

Command:

```text
python3 scripts/probes/probe_r290_constrained_sextic_average.py \
  --summary --lag-check-limit 0 \
  --cells 193:8,577:8,1489:8,1153:16,4129:16,5953:32
```

Output, normalized by `scale = m^3 q^3`:

```text
      p    n     m  beta        E3      Wick    Generic  Collision     C21x21    C111x21     Ccube  Connected
    193    8    24  2.53    3.0190    4.3160    -1.2305    -0.0664    -0.1740    +0.1533   -0.0458    -1.2970
    577    8    72  3.06   13.9699    5.3968    +8.6615    -0.0883    -0.0237    -0.0790   +0.0144    +8.5731
   1489    8   186  3.51   12.8841    5.7614    +6.9716    +0.1511    -0.0042    +0.1601   -0.0048    +7.1227
   1153   16    72  2.54    5.1654    5.3966    +0.3312    -0.5624    +0.0158    -0.5776   -0.0006    -0.2312
   4129   16   258  3.00   18.9503    5.8273   +12.6086    +0.5144    -0.0037    +0.5196   -0.0015   +13.1230
   5953   32   186  2.51   10.9207    5.7613    +5.6316    -0.4722    -0.0167    -0.4512   -0.0043    +5.1594
```

## Consequence

The cube-cube R41/R57/R60 path is not just incomplete; it focuses on a bucket that is
empirically tiny in this signed constrained expansion.  The right collision proof order is:

1. `C111x21`: mixed five-point distinct/repeated constrained estimate.
2. `C21x21`: four-point repeated/repeated estimate.
3. `Ccube`: cube-involving lower-order cleanup.

After this, the only large term left is still the R293 generic fully distinct connected
six-point subconvexity theorem.
