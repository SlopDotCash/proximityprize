# #466 R262 survivor actual-mass refutation

## Question

R261 refuted a positive weighted fine-tail bound for the n=64 large-index
obstruction.  This follow-up asks whether the same survivor sets are merely an
artifact of the weighted envelope, or whether they also carry dangerous positive
mass after the fine residual is exponentiated.

For the trimmed fine layer

```text
R = X64 - lift(X32),
```

the probe scans thresholds on `R` after deleting the largest fine spike and
records

```text
W(theta) = sum_{R >= theta} exp(lift(X32) / 4) / M,
A(theta) = sum_{R >= theta} exp((lift(X32) + R) / 4) / M.
```

It reports the half-rate scaled diagnostics

```text
weightedC = W(theta) * exp(theta / 2),
actualC   = A(theta) * exp(theta / 2).
```

These constants are tail-envelope diagnostics, not the full MGF values.

## Command

```bash
python3 scripts/probes/probe_r262_n64_survivor_actual_mass.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --trim 1 --tau 0.5 --sort actual_c --top 15

python3 scripts/probes/probe_r262_n64_survivor_actual_mass.py \
  --min-index 512 --max-index 12000 --chunk 8192 \
  --trim 1 --tau 0.5 --max-exact-mgf 2.0 \
  --sort actual_c --top 15
```

## Result

Unfiltered worst case:

```text
worst_actual_c=399.11338467 M=10900 p=697601 weightedC=7.04823660
theta=16.146 count=1 exactMGF=2.2184 fineMax=18.690
```

The next worst rows are also large:

```text
M=10404 p=665857 actualC=244.2205 weightedC=6.1290 ratio=39.8467
M=1024  p=65537  actualC=236.2568 weightedC=19.8606 ratio=11.8958
```

Even after filtering to exact `n=64` MGF at most `2`, the positive survivor
constant remains much too large:

```text
worst_actual_c=31.01840747 M=2227 p=142529 weightedC=1.59235133
theta=11.877 count=1 exactMGF=1.8710 fineMax=11.914
```

Representative remaining rows:

```text
M=1030 p=65921  actualC=21.0918 weightedC=1.8836 ratio=11.1974
M=6255 p=400321 actualC=18.9019 weightedC=1.5323 ratio=12.3369
M=4050 p=259201 actualC=17.4066 weightedC=1.3048 ratio=13.3405
M=3760 p=240641 actualC=17.0025 weightedC=1.2662 ratio=13.4288
M=6583 p=421313 actualC=16.7032 weightedC=0.9655 ratio=17.3005
```

## Conclusion

The positive layer-cake route is refuted in this form.  Exponentiating the fine
residual amplifies the single high-residual survivors instead of washing them
out, and this remains true after excluding rows whose exact MGF already exceeds
`2`.

Any repair now has to structurally remove or pay these isolated fine residual
spikes, or move before exponentiation to a signed character-level decomposition.
There is no useful positive-mass cancellation on the survivor sets measured
here.
