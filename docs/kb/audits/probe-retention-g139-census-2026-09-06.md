# Retention mapping: G139 accident census — 2026-09-06

The complete replay of `scripts/probes/probe_g139_production_accident_census.py`
passed and matches `scripts/probes/_out_g139_production_accident_census.txt`
byte for byte. These two artifacts remain retained. The original unreferenced
cohort is now 40 of 92 reviewed, with 52 remaining.

This script had the same integer-root rounding bug found in the Phi probe:
it compared gaps between powers rather than the half-integer midpoint of the
root. The same exact midpoint correction applies. The regression tests now run
the rounding cases against both implementations. The sampled prime choices and
all census outputs remain unchanged.

At n=16,32,64,128,256 the selected cells have respectively 45,93,189,381,765
solutions of a+b=c+1, all within the three specified lawful families. The
G173 cross-check at n=64,p=17318209 has 213 solutions and 24 accidents, including
the exact witness (5663213,17079628,5424631). The counts use modular integer
arithmetic; only the displayed scale logarithm is floating point. These finite
cells do not establish any uniform bound or production n=2^30 claim.

The search for duplicated helper bugs also found the missing Miller–Rabin base
in `scripts/probes/probe_w16_tz_prize_scale.py`. Its base list and header now include
41, matching the 13-base cutoff documented by [Sorenson and Webster, Theorem 1.1](https://arxiv.org/html/1509.00864v1).
The known composite regression now runs against both primality helpers. The W16
full experiment was not replayed, and its historical output and generated Lean
files are not certified by this audit. It is outside this two-artifact cohort increment.
