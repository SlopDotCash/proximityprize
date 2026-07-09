# #466 R301 — n=128 piecewise shoulder cap: late window COMPLETE (M=50001..80000, zero formula escapes)

## Question

Finish the R296 formula-cap verification window. R298 covered `M=50001..68444`,
R299 extended to `M=73694`; this run closes the remainder.

## Command

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 73695 --max-index 80000 \
  --progress-every-primes 200 --progress-every-seconds 30 --top 32
```

Completed in 883s (789 primes, 3054 candidate rows, 1521 high rows, highMass 1.1966).

## Result

```text
cap(M) = 8192 * ceil((M + 10000) / 15000)      (= 49152 throughout this segment)

formula residual: count = 0, mass = 0          <- ZERO escapes
prevCap residual: count = 7, mass = 0.001701   (worst 0.000264 @ M=78036 p=9988609)
```

Combined with R298 + R299, the full late window is now verified:

```text
M = 50001..80000 : formula residual mass = 0   (COMPLETE, no partial prefix remains)
```

The seven residual rows escape only the PREVIOUS (pre-R296) cap, all in the
fineRatio ≈ 0.75 band with tail/top ≈ 0.087–0.090, comfortably inside the new formula cap
(their masses ≤ 2.7e-4 ≪ band budget).

## Status

The R291–R296 empirical shoulder ladder for n=128 high-fineRatio moderate rows is now an
executable formula cap verified escape-free across `M = 50001..80000`. This is numerical
lane evidence (probe, not a theorem): the next step, if the lane continues, is either
extending below M=50000 (where R296–R297 already fitted the earlier piecewise rungs) or
promoting the formula cap to a named `Prop` consumed by the punctured-list budget sockets.
CORE OPEN — this is budget bookkeeping for the n=128 shoulder, not wall contact.
