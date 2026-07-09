# #466 R310 — executable classifier confirms the full `c=3` histogram at n=32,64,128

## Target

R308 exposed the conjectural `c=3` relation-web histogram:

```text
delta = 24n - 18   count = n
delta = 90         count = 2n
delta = 36         count = n(n-7)
```

R309 proved in Lean that this histogram implies excess `60n² - 90n`, beating exact-Wick
headroom for every `n >= 4`.  R310 turns the histogram itself into an executable classifier.

## Probe

New script:

```text
scripts/probes/probe_r310_c3_histogram_classifier.py
```

For a given `n,p`, it:

1. builds the R305 char-zero depth-3 shadow histogram;
2. finds the exponent `d` with `g^d = 3` for an order-`n` element `g`;
3. computes the full positive collision-delta histogram under the mod-`p` pushforward;
4. compares it to the predicted three-stratum histogram above.

## Results

Commands:

```bash
python3 scripts/probes/probe_r310_c3_histogram_classifier.py --n 32 \
  --p 21523361
python3 scripts/probes/probe_r310_c3_histogram_classifier.py --n 64 \
  --p 926510094425921
python3 scripts/probes/probe_r310_c3_histogram_classifier.py --n 128 \
  --p 1716841910146256242328924544641
```

Outputs:

```text
scripts/probes/_out_466_r310_n32_c3_classifier.txt
scripts/probes/_out_466_r310_n64_c3_classifier.txt
scripts/probes/_out_466_r310_n128_c3_classifier.txt
```

All three cases have `d = 21` and match the predicted histogram exactly:

```text
n=32:
  delta=750  count=32   mass=24000
  delta=90   count=64   mass=5760
  delta=36   count=800  mass=28800
  excess=58560, headroom=44800

n=64:
  delta=1518 count=64   mass=97152
  delta=90   count=128  mass=11520
  delta=36   count=3648 mass=131328
  excess=240000, headroom=181760

n=128:
  delta=3054 count=128   mass=390912
  delta=90   count=256   mass=23040
  delta=36   count=15488 mass=557568
  excess=971520, headroom=732160
```

## Interpretation

The R305/R307 high-beta exact-Wick failures at `n=32,64,128` are not unrelated accidents.
They are the same orbit-counting object:

```text
ζ^21 = 3
```

acting on the char-zero depth-3 shadow support.  The classifier collapses the relation-web
problem to a precise finite orbit-counting theorem:

```text
C3RelationWebHistogram21:
  if an order-n element g satisfies g^21 = 3 and no extra low-height relations collapse
  the listed fibers, then the positive pushforward collision histogram is exactly
  {24n-18 ↦ n, 90 ↦ 2n, 36 ↦ n(n-7)}.
```

This is now the clean proof target.  The next Lean move is not analytic number theory; it is
formal finite combinatorics of signed-basis 3-sum shadow vectors under the rewrite
`e_{i+21} = 3 e_i` and its inverse/negative companions.

No prize closure claimed.  This gives a sharper obstruction template for the dead fixed-depth
exact-Wick route and a concrete finite combinatorics target to prove or break.
