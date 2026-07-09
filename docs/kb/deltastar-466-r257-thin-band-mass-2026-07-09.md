# #466 R257: thin-band mass between 0.75 and q60 cap

Date: 2026-07-09

## Question

R253/R256 suggest using the quantile cap

```text
S(0.79049) <= 0.40
```

as a clean proxy for `Q_0.60 <= 0.79049`. But the R251 micro-band needs
`S(0.75) <= 0.412121...`, so one also needs to control the thin band
`[0.75, 0.79049)`.

Command:

```bash
python3 scripts/probes/probe_r257_thin_band_mass.py --cache-only
```

## Result

Worst micro-band rows:

```text
micro    band     Slo      Shi      n     p          M
0.601134 0.013468 0.412121 0.398653 512   760321     1485
0.601039 0.015690 0.412056 0.396367 512   620033     1211
0.600614 0.019608 0.411765 0.392157 512   417793     816
```

Worst thin-band rows are not the same as the worst micro rows:

```text
band     micro    Slo      Shi      n     p          M
0.025185 0.568327 0.389630 0.364444 512   345601     675
0.025000 0.578244 0.396429 0.371429 512   286721     560
0.024316 0.554192 0.379939 0.355623 1024  673793     658
```

Summary:

```text
band median=0.012410 p95=0.017049 max=0.025185
Slo  median=0.384344 p95=0.396721 max=0.412121
Shi  median=0.371819 p95=0.383980 max=0.398653
```

Correlations with the micro-band score:

```text
band +0.197435
Shi  +0.950098
Slo  +1.000000
```

## Route update

The q60 cap alone does not imply the R251 micro-band cap. The honest split is:

```text
S(0.79049) <= 0.3987
mass in [0.75, 0.79049) <= 0.0135
```

for the worst main-lane rows, or a slightly rounded theorem-grade version whose
sum stays below the R251 budget. The thin-band mass is not the main obstruction,
but it cannot be ignored.
