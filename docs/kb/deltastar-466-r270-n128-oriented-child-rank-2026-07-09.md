# #466 R270 n=128 oriented child rank

## Question

R269 refined the moderate near-doubling branch to oriented same-phase joins.
This probe asks whether the event is simply a collision of two top-ranked n=64
children inside the same n=128 parent.

For every near-doubling row it ranks both n=64 children globally by `X64`.

## Command

```bash
python3 scripts/probes/probe_r270_n128_oriented_child_rank.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine128 10 \
  --fine-ratio-cut 0.75 --top 25
```

## Result

```text
near rows=136
near mass=1.86531933
bestRank median=3
worstRank median=545
maxWorstRank=3040
```

Both-children-in-top-k coverage:

```text
both <= 4:   count=1  mass=0.129143
both <= 8:   count=1  mass=0.129143
both <= 16:  count=2  mass=0.176659
both <= 32:  count=4  mass=0.343600
both <= 64:  count=7  mass=0.486186
both <= 128: count=12 mass=0.682371
```

Worst near rows:

```text
p=288257 M=2252 mass=0.129143 ranks=(1,4)
p=222337 M=1737 mass=0.088208 ranks=(20,1)
p=158209 M=1236 mass=0.078733 ranks=(21,2)
p=183041 M=1430 mass=0.076779 ranks=(37,1)
p=95233  M=744  mass=0.055211 ranks=(94,2)
p=116993 M=914  mass=0.048577 ranks=(97,1)
p=517249 M=4041 mass=0.047517 ranks=(15,5)
```

## Conclusion

The top-top collision hypothesis is false.  One child is usually extremely
high-ranked, but the partner can live far down the n=64 list.  Even top-128
captures only `12/136` near rows and mass `0.682371` out of `1.865319`.

The branch target is now sharper:

```text
oriented near-doubling = top child + aligned tail child,
```

not top child + top child.  A proof must count, for each high n=64 child, how
many tail children in the opposite n=64 coset are same-phase and large enough
to create fine gain.  This is closer to a conditional tail-around-spike
statement than to a global top-k collision bound.
