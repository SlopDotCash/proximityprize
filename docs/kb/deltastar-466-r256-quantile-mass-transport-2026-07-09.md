# #466 R256: quantile mass-transport balances

Date: 2026-07-09

## Question

R255 reframed the trim-five `q60` cap as a lower-bulk / mass-transport
phenomenon. R256 tests explicit hinge balances above and below `q60`, `0.75`,
and the candidate cap `Q* = 0.79049`.

Command:

```bash
python3 scripts/probes/probe_r256_quantile_mass_transport.py --cache-only
```

## Result

Worst micro-band rows:

```text
micro    q60      mean     Aq60     Bq60     Aq/Bq    A075     B075     A/B075   S@Q*
0.601134 0.790489 0.96965  0.50871  0.32955  1.5437   0.52521  0.30555  1.7189   0.400000
0.601039 0.783391 0.96497  0.51058  0.32900  1.5519   0.52418  0.30920  1.6953   0.398010
0.600614 0.779684 0.95986  0.50275  0.32258  1.5586   0.51491  0.30505  1.6880   0.394575
```

Correlations with the micro-band score:

```text
S@Q*     +0.946815
q60      +0.937601
Bq60     +0.896598
Aq/Bq    -0.837986
B@Q*     -0.740639
B075     -0.713741
Aq60     -0.520807
A/B075   +0.431637
```

Simple transport ratios are not the right invariant: the largest `Aq/Bq`
occurs far from the obstruction:

```text
Aq/Bq=2.48997042 micro=0.49247138 q60=0.58098058 n=1024 p=715777 M=699
```

## Route update

The useful signal is lower-bulk mass itself (`Bq60`, `S@Q*`), not an
above/below transport ratio. The q60 cap remains the cleanest formulation:

```text
S(0.79049) <= 0.40
```

equivalently `Q_0.60 <= 0.79049`, for the trim-five residual main lane.
