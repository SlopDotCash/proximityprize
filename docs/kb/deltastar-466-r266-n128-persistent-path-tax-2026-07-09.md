# #466 R266 n=128 persistent-path tax

## Question

R265 left a plausible n=64 socket: after filtering exact-MGF offender rows,
persistent coherent dyadic paths carried modest positive MGF mass.  This note
tests whether the same path-tax idea scales to the next dyadic level, using

```text
R = X128 - lift(X64)
```

and tracing larger-child ancestry through

```text
8 -> 16 -> 32 -> 64 -> 128.
```

## Commands

Small calibration:

```bash
python3 scripts/probes/probe_r266_n128_persistent_path_tax.py \
  --min-index 512 --max-index 2500 --chunk 4096 \
  --top-per-row 4 --min-fine 10 \
  --t8 4 5 6 --t16 7 9 --t32 10 12 --t64 12 14 --top 20
```

Larger first scaling check:

```bash
python3 scripts/probes/probe_r266_n128_persistent_path_tax.py \
  --min-index 512 --max-index 6000 --chunk 4096 \
  --top-per-row 4 --min-fine 10 \
  --t8 4 5 6 --t16 7 9 --t32 10 12 --t64 12 14 --top 20
```

## Calibration result: M <= 2500

The coherent-path signal persists:

```text
cached_rows=34
path rows=39
maxFine=14.27673170
allJoinsGe=39/39
medianMinCos=1.00000000
minMinCos=1.00000000
```

The n=64 thresholds were too high for n=128 and captured nothing.  Lower
thresholds captured a few rows:

```text
t8=4 t16=7 t32=10 t64=12: captured=5 worstMass=0.07677915 at M=1430
t8=4 t16=9 t32=10 t64=12: captured=1 worstMass=0.00613238 at M=2372
```

## Scaling check: M <= 6000

The larger scan still has almost perfect path coherence:

```text
cached_rows=187
path rows=233
maxFine=24.28152886
allJoinsGe=231/233
medianMinCos=1.00000000
minMinCos=-1.00000000
maxExactMGF=1.7528
```

But the path tax is no longer small:

```text
t8=4 t16=7 t32=10 t64=12: captured=51 worstMass=0.18758511 at M=5202
t8=4 t16=9 t32=10 t64=12: captured=24 worstMass=0.18103322 at M=5202
t8=6 t16=9 t32=12 t64=14: captured=8  worstMass=0.18103322 at M=5202
```

The decisive row is

```text
p=665857, M128=5202, exactMGF128=1.686315
idx=438 fine=23.515336 X128=27.390895
x64 children=(3.875559, 29.511756)
best64=29.511756 best32=14.771600 best16=11.897539 best8=7.338783
cos128=cos64=cos32=cos16=1.000000
single-path mass=0.18103322
```

This is the same prime that appears as an n=64 resonance row
`p=665857, M64=10404`.

## Conclusion

The path-coherence object scales: high fine spikes at n=128 are again supported
on persistent same-sign dyadic branches.  However, the R265 finite-branch
accounting does **not** scale naively.  Filtering by exact MGF at the current
level is too weak, because `p=665857` has exact n=128 MGF below 2 while still
carrying a large coherent-path contribution.

The next theorem cannot be just:

```text
current-level exact MGF <= 2  +  persistent-path threshold tax.
```

It needs a cross-level resonance taxonomy: a row like `p=665857` is already a
bad/coherent ancestor at n=64 and must be paid or structurally classified by
the lower-level tower data.  The promising object is now a multilevel
resonance tree, not a per-level tail split.
