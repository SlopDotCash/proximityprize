# #466 R298 n=128 piecewise shoulder partial late check

## Question

R297 checked the formula cap

```text
cap(M) = 8192 * ceil((M + 10000) / 15000)
```

on `M=30001..50000` and found no formula escapes.  R298 started the larger
late-window check:

```text
M=50001..80000
```

The run was intentionally stopped after it became too long for a single turn,
but it produced useful partial evidence.

## Command

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 50001 --max-index 80000 \
  --progress-every-primes 200 --progress-every-seconds 30 --top 32
```

Interrupted after the last completed progress report:

```text
progress M=68444 primes=2329 high=4305 highMass=4.060377
formulaMass=0.000000 prevMass=0.004025 cap=49152 elapsed=1738.3s
```

## Result So Far

On the completed portion:

```text
M = 50001..68444
formula residual mass = 0
previous-cap residual mass = 0.004025
```

The formula cap advanced from `40960` to `49152` at the expected transition
and remained clean through `M=68444`.

The observed previous-cap residual is the same tiny boundary already recorded
in R294:

```text
tailRank > 32768, but tailRank <= 40960
mass = 0.004025
```

No row escaping the formula cap was observed.

## Conclusion

This is partial evidence, not a completed full-window verification.  It extends
the checked formula-cap range from R297 into the late window:

```text
formula cap clean on:
  30001..50000  (complete, R297)
  50001..68444  (partial, R298)
```

The next run should continue from:

```text
M = 68445..80000
```

If that continuation is also clean, then the formula cap is empirically verified
over the combined range `30001..80000`.

