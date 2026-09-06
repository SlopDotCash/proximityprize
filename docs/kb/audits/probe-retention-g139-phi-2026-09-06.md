# Retention mapping: G139 Phi certificates — 2026-09-06

The complete corrected replay of `scripts/probes/probe_g139_phi_certificate.py`
passed and matches `scripts/probes/_out_g139_phi_certificate.txt` byte for byte.
Both original unreferenced artifacts remain retained. This brings the reviewed
cohort to 38 of 92, with 54 remaining. The JSON records hashes and complete output.

The audit found two reproducible helper bugs:

- The primality checker used 12 bases (through 37) with the 13-base cutoff.
  It returned true for the composite 318665857834031151167461, whose factors
  399165290221 and 798330580441 multiply to that value. Adding base 41 rejects
  it and matches the claimed strict cutoff 3317044064679887385961981.
  These bounds are Theorem 1.1 of [Sorenson and Webster](https://arxiv.org/html/1509.00864v1).
- Root rounding compared distances between integer powers rather than the root
  and its half-integer midpoint. It returned 1 for the cube root of 4, which
  exceeds 3/2 since 4 > (3/2)^3. The helper now uses exact scaled midpoint
  comparisons and round-to-even ties. Neither correction changes this archive.

Three regression tests cover the composite, strict cutoff, and rounding cases.

All eight diagonal cells n=8192 through 1048576 have n/2 distinct Phi values.
The first three use the first prime in the odd-quotient progression p=1+n*q
above the rounded target; the larger five use explicit primes checked by
Pocklington with their supplied complete p-1 factorizations. The two accident
cells (64,17318209) and (512,138027521) each retain three collisions. Arithmetic,
subgroup order, and image comparison are exact; no floating FFT is used.

This audit replays the finite Phi table and the implementation's primality
certificates. It does not formalize the Phi-to-weak-Sidon implication in Lean,
prove an all-primes claim, or reach the production n=2^30 gate in issue #164.
