# #466 R299 n=128 piecewise shoulder late-prefix check

## Question

R298 partially checked the formula cap

```text
cap(M) = 8192 * ceil((M + 10000) / 15000)
```

on `M=50001..68444`, with no formula escapes.  R299 continues from:

```text
M=68445
```

## Command

```bash
python3 scripts/probes/probe_r296_n128_piecewise_shoulder_cap.py \
  --min-index 68445 --max-index 80000 \
  --progress-every-primes 200 --progress-every-seconds 30 --top 32
```

The run was stopped after the last completed progress line:

```text
progress M=73694 primes=643 high=1206 highMass=1.002008
formulaMass=0.000000 prevMass=0.000000 cap=49152 elapsed=1297.8s
```

## Result So Far

On the completed continuation prefix:

```text
M = 68445..73694
formula residual mass = 0
previous-cap residual mass = 0
cap(M) = 49152 throughout the reported prefix
```

Combined with R298:

```text
M = 50001..73694
formula residual mass = 0
```

The earlier previous-cap boundary mass from R298 remains:

```text
previous-cap residual mass = 0.004025
```

and no new previous-cap escapes appeared in this continuation prefix.

## Conclusion

This is another partial checkpoint, not a completed full-window verification.
It extends the formula-clean late range to:

```text
M = 50001..73694
```

The next continuation should start at:

```text
M = 73695
```

to finish the remaining `73695..80000` segment.

