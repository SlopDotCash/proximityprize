# #466 R250: trim-count slack check

Date: 2026-07-09

## Question

R249 leaves a knife-edge trim-five micro-band certificate. R250 checks whether
deleting more than five top quotient values buys useful residual slack once the
exact top contribution is charged.

Command:

```bash
python3 scripts/probes/probe_r231_top_spike_trimmed_mgf.py \
  --medium-min-a 8 --medium-max-a 10 --medium-max-index 4096 \
  --min-index 512 --chunk 8192 --cache-dir .cache/proximity-r231 --cache-only \
  --trims 5 6 7 8 10 --taus 0.75 --spike-budgets 0 \
  --step 0.03125 --cutoff 0 --top 20
```

## Result

```text
budget   slack    C_req    trim
1.9950   0.0050   0.60111  5
1.9996   0.0004   0.59948  6
2.0047  -0.0047   0.59850  7
2.0096  -0.0096   0.59752  8
2.0175  -0.0175   0.59556  10
```

Deleting extra spikes slightly lowers the residual tail constant, but the exact
top contribution rises faster. Trim five remains the best total MGF budget.

## Route update

The R249 finite certificate should stay at trim five. The live proof shape is:

```text
top-five exact contribution
+ trim-five micro-band residual cap on [0.75, 0.755)
+ trim-five high-tail residual cap from 0.755
```

Trim six has only `0.0004` total slack and is too fragile; trim seven and above
already fail the target budget.
