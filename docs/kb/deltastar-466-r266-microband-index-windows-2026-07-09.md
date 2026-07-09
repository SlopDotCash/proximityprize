# #466 R266: micro-band by quotient-index windows

Date: 2026-07-09

## Question

R251's micro-band cap is knife-edge. R266 asks whether the obstruction is
confined to a finite quotient-index window.

Command:

```bash
python3 scripts/probes/probe_r266_microband_index_windows.py \
  --max-index 5000 --bucket-width 512
```

## Result

Overall worst rows:

```text
micro    slack    S        n     p          M
0.601134 0.000066 0.412121 512   760321     1485
0.601039 0.000161 0.412056 512   620033     1211
0.600614 0.000586 0.411765 512   417793     816
0.594872 0.006328 0.407828 256   202753     792
```

By `M` bucket:

```text
bucket       worst    slack
0513-1024    0.600614 0.000586
1025-1536    0.601134 0.000066
1537-2048    0.591086 0.010114
2049-2560    0.587936 0.013264
2561-3072    0.584441 0.016759
3073-3584    0.585947 0.015253
3585-4096    0.583992 0.017208
4097-4608    0.579812 0.021388
4609-5120    0.580128 0.021072
```

The knife-edge rows are confined to `M < 1536`, especially `n=512`. Starting at
`M >= 1537`, the cached/extended data has at least `0.0095` slack.

## Route update

This is the first useful structural split for the micro-band target:

```text
finite medium-index branch:
  M < 1536, with worst rows at n=512;

large-index branch:
  M >= 1537, where the micro-band cap appears to have comfortable slack.
```

The next theorem search should avoid explaining the knife-edge uniformly. A
finite certificate for `M < 1536` plus a softer large-index vertical
distribution theorem may be enough.

## Wider large-index stress

Command:

```bash
python3 scripts/probes/probe_r266_microband_index_windows.py \
  --min-index 1537 --max-index 8000 --bucket-width 1024 --chunk 8192 --top 10
```

Output:

```text
overall worst for M >= 1537:
micro    slack    S        n     p          M
0.591086 0.010114 0.405233 1024  1604609    1567
0.587936 0.013264 0.403073 512   1299457    2538
0.586223 0.014977 0.401899 512   2912257    5688
```

The large-index branch remains comfortably below the target through `M = 8000`.
There are secondary bumps, but none approach the `M < 1536` knife-edge.
