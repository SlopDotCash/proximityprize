# R229: one-band MGF cutoff scan

Status: obstruction map for the R226 one-band/twelve-spike route.

## Probe

Script:

```text
scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py
```

It evaluates exact quotient spectra and reports:

- `mgf1/4`: the exact empirical normalized quotient quarter-MGF.
- `env_budget`: the closed staircase budget from the R226 envelope
  `tau=1`, `C=3/5`, `K=12`.

## Main medium sweep

Command:

```bash
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode medium --medium-max-a 11 --medium-max-index 512 \
  --step 0.125 --top 30
```

Result:

```text
tested=928
env_failures=615
mgf_failures=2

mgf=2.752305 env=19.271132 maxX=20.690520 M=124 n=64  p=7937
mgf=2.306785 env=12.776944 maxX=24.486519 M=512 n=128 p=65537
```

The direct MGF fails rarely; the envelope budget fails very often at small
`M` because the `K/M` spike term is too pessimistic when integrated to the
observed maximum.

## Larger mixed sweep

Command:

```bash
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode mixed --medium-max-a 11 --medium-max-index 4096 --min-index 513 \
  --ns 16 32 64 128 256 --min-p 65537 --max-p 5000000 \
  --limit-per-n 80 --step 0.125 --top 35
```

Result:

```text
tested=5654
env_failures=889
mgf_failures=6
worst_mgf=3.262396 n=64 p=65537 M=1024 maxX=29.776100
```

Top direct-MGF failures in the near range:

```text
mgf=3.262396 env=22.446739 maxX=29.776100 M=1024 n=64  p=65537
mgf=2.306785 env=12.776944 maxX=24.486519 M=512  n=128 p=65537
mgf=2.2387   env=10.2262   maxX=24.992    M=757  n=64  p=48449
mgf=2.0015   env=7.5724    maxX=24.556    M=990  n=64  p=63361
```

A targeted `n=64` scan above `M=1100` found one further direct failure:

```bash
python3 scripts/probes/probe_r229_one_band_mgf_cutoff_scan.py \
  --mode medium --medium-max-a 6 --medium-max-index 10000 \
  --min-index 1101 --sort mgf --fail-only mgf --top 30
```

Failure:

```text
mgf=2.632067 env=13.701201 maxX=32.121199 M=3193 n=64 p=204353
```

Follow-up windows were clean for direct MGF:

```text
M=3194..6000: 1917 rows, mgf_failures=0, worst_mgf=1.623435
M=6001..10000: 2665 rows, mgf_failures=0, worst_mgf=1.667023
```

## Interpretation

The R226 tail shape is not the final proof by itself.  There are rare
spike-resonant quotient spectra with direct quarter-MGF above `2`, especially
for `n=64` and Fermat-style rows involving `p=65537`.

The analytic envelope is much weaker than the exact MGF: it fails hundreds of
rows where the exact MGF is safely below `2`.  The next proof route should
therefore avoid integrating a crude fixed `K/M` term all the way to `maxX`.
Likely options:

- a finite exceptional-resonance branch for the few direct MGF failures;
- a high-spike ancestry/counting lemma that prices the top spikes by rank
  instead of a flat `K`;
- a hybrid certificate using exact finite MGF for bounded `M` and the
  one-band quotient tail only after a proven large-index cutoff.

Current best obstruction family to attack directly:

```text
n=64, p=7937   M=124
n=64, p=48449  M=757
n=64, p=63361  M=990
n=64, p=65537  M=1024
n=64, p=204353 M=3193
n=128, p=65537 M=512
```
