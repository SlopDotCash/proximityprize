# #466 R270: verify finite micro-band certificate

Date: 2026-07-09

## Purpose

R270 verifies the R269 CSV certificate for the finite branch `512 <= M < 1536`.

Command:

```bash
python3 scripts/probes/probe_r270_verify_finite_microband_certificate.py
```

Output:

```text
R270 verify finite micro-band CSV rows=465 failures=0
worst micro=0.601133782897 slack=0.000066217103 n=512 p=760321 M=1485 count=612
```

## Route update

The finite branch now has:

1. a generator: `scripts/probes/probe_r269_finite_microband_certificate_csv.py`;
2. a data artifact:
   `docs/kb/data/deltastar-466-r269-finite-microband-certificate.csv`;
3. a verifier: `scripts/probes/probe_r270_verify_finite_microband_certificate.py`.

This is not yet a Lean-native certificate, but it is a reproducible finite
check that can be promoted later.
