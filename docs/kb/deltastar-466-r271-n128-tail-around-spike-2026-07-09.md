# #466 R271 n=128 tail around spike

## Question

R270 refuted a symmetric top-top collision certificate.  The near-doubling
branch looked like

```text
top n=64 child + aligned tail n=64 child.
```

This probe measures that conditional tail around top children.  For each
near-doubling row it records:

```text
top_rank  = better rank of the two n=64 children,
tail_rank = worse rank of the two n=64 children,
top_x64, tail_x64.
```

## Command

```bash
python3 scripts/probes/probe_r271_n128_tail_around_spike.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 \
  --fine-ratio-cut 0.75 --top 25
```

## Result

```text
rows=136
total_mass=1.86531933
topRank median=3
tailRank median=545
tailX median=3.187308
tail/top median=0.251003
```

Top-child coverage:

```text
topRank <= 1:  count=26  mass=0.591415
topRank <= 2:  count=52  mass=1.036651
topRank <= 4:  count=92  mass=1.408775
topRank <= 8:  count=129 mass=1.801419
topRank <= 16: count=135 mass=1.859712
```

Tail-rank coverage is much weaker:

```text
tailRank <= 32:   count=4   mass=0.343600
tailRank <= 64:   count=7   mass=0.486186
tailRank <= 128:  count=12  mass=0.682371
tailRank <= 256:  count=26  mass=0.903528
tailRank <= 512:  count=66  mass=1.393814
tailRank <= 1024: count=103 mass=1.688468
```

Tail-value coverage:

```text
tailX >= 2:  count=110 mass=1.705042
tailX >= 4:  count=41  mass=0.946160
tailX >= 6:  count=7   mass=0.486186
tailX >= 8:  count=2   mass=0.176659
tailX >= 10: count=1   mass=0.129143
```

Worst rows:

```text
p=288257 M=2252 mass=0.129143 topRank=1 tailRank=4   topX=11.99 tailX=10.72
p=222337 M=1737 mass=0.088208 topRank=1 tailRank=20  topX=13.15 tailX=7.38
p=158209 M=1236 mass=0.078733 topRank=2 tailRank=21  topX=11.30 tailX=7.23
p=183041 M=1430 mass=0.076779 topRank=1 tailRank=37  topX=13.51 tailX=6.02
p=95233  M=744  mass=0.055211 topRank=2 tailRank=94  topX=12.60 tailX=3.61
p=198529 M=1551 mass=0.025686 topRank=1 tailRank=281 topX=14.17 tailX=2.77
```

## Conclusion

This branch has a clean asymmetric shape:

```text
top child rank <= 8  +  long aligned tail partner.
```

The symmetric rank-window certificate is false, but the top-child spine is very
strong: top 8 n=64 children account for `1.801419 / 1.865319` of near-branch
mass.  The hard part is the conditional aligned tail distribution in the
opposite half.

The next theorem target should be:

```text
For each of the top O(1) n=64 children, bound the same-phase opposite-half
tail values that can pair with it to create near-doubling at n=128.
```

This is narrower than global positive tails and should be expressible as a
conditional tail-around-spike statement.
