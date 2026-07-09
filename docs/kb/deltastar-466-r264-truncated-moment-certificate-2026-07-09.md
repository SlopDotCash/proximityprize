# #466 R264: truncated moment certificates

Date: 2026-07-09

## Question

R243 refuted ordinary low moments as a route to the micro-band cap. R264 tests
threshold-aware hinge moments around `theta = 0.75`:

```text
E[(X-theta)_+^k], E[(theta-X)_+^k].
```

Command:

```bash
python3 scripts/probes/probe_r264_truncated_moment_certificate.py --cache-only
```

## Result

Worst rows:

```text
micro    S        p1       n1       p1/n1   p2/p1   n2/n1   mean
0.601134 0.412121 0.52521  0.30555  1.7189   2.6419   0.6094   0.96965
0.601039 0.412056 0.52418  0.30920  1.6953   2.6233   0.6162   0.96497
0.600614 0.411765 0.51491  0.30505  1.6880   2.4425   0.6073   0.95986
```

Correlations with the micro-band score:

```text
S        +1.000000
n1       -0.713741
n2       -0.558568
p1/n1    +0.431637
p2/p1    -0.273836
mean     +0.270201
p1       -0.021886
```

The largest hinge ratios occur away from the obstruction:

```text
p1/n1=1.76676945 micro=0.57540727
p2/p1=3.39761450 micro=0.54229087
```

## Route update

Truncated moments are better aligned than raw moments, but they still do not
produce a new certificate. The strong signal is the below-threshold hinge mass
`n1`, which is essentially another encoding of how much mass lies below
`0.75`.

No threshold-aware low-degree moment shortcut survives here.
