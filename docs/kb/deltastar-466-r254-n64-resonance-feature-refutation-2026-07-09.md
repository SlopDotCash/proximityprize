# R254 n=64 resonance feature refutation

Date: 2026-07-09
Issue: #466 / Proximity Prize

## Question

R253 showed that the beta-gated rank-sum route is destroyed by an `n=64`
large-index resonance family.  R254 asks whether the bad rows can be isolated
by simple arithmetic features of `M=(p-1)/64` or `p`: factorization, residue
classes, valuations, or closeness to a square.

## Probe

New script:

```text
scripts/probes/probe_r254_n64_resonance_features.py
```

It scans prime rows `p=64M+1` and reports:

```text
top8/top16 rank mass, full quarter-MGF, max X,
factor counts omega/Omega, largest prime factor,
v2(M), v3(M), residues mod 3/5/7, and square distance.
```

## Commands

```bash
python3 -m py_compile scripts/probes/probe_r254_n64_resonance_features.py
python3 scripts/probes/probe_r254_n64_resonance_features.py \
  --min-index 512 --max-index 12000 --chunk 8192 --sort top8 --top 25
python3 scripts/probes/probe_r254_n64_resonance_features.py \
  --min-index 512 --max-index 12000 --chunk 8192 --sort mgf4 --top 25
python3 scripts/probes/probe_r254_n64_resonance_features.py \
  --min-index 512 --max-index 12000 --chunk 8192 --sort max --top 12
```

## Findings

No simple feature isolates the resonance family.

The worst rows by top-rank mass include:

```text
M=1024  p=65537   top8=1.8906  M=2^10
M=3193  p=204353  top8=1.1819  M=31*103
M=757   p=48449   top8=0.9218  M prime
M=10900 p=697601  top8=0.6780  M=2^2*5^2*109
M=10404 p=665857  top8=0.6594  M=102^2
```

The worst rows by maximum spike include:

```text
M=10900 p=697601  maxX=34.0594  square distance 84
M=10404 p=665857  maxX=33.2194  square distance 0
M=3193  p=204353  maxX=32.1212  square distance 56
M=1024  p=65537   maxX=29.7761  square distance 0
M=6583  p=421313  maxX=26.0995  square distance 22
M=11685 p=747841  maxX=26.0649  square distance 21
```

The near-square hypothesis is therefore only a clue, not a classifier: exact
or near squares appear, but so do prime, semiprime, high-power, and generic
composite indices.

Residues mod `3,5,7` and small valuations are similarly non-decisive across
the top rows.

## Route update

The `n=64` obstruction is not a cheap arithmetic family in `M`.  A viable next
attack needs to inspect the actual phase/cyclotomic structure of the top
Gauss-period representatives, for example:

```text
compare top representatives across bad rows in a common cyclotomic coordinate;
look for low-dimensional phase alignment or stationary-phase witnesses;
decompose the n=64 spectrum into characters/factors rather than scalar M features.
```

This keeps R253's conclusion: the rank-sum proof shape cannot be rescued by
excluding an obvious factorization/residue class.
