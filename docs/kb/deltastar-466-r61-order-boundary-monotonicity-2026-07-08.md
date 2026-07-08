# δ* #466 — order-boundary map for normalized monotonicity (2026-07-08)

## Hypothesis

R58/R59 found that the Wick-normalized moment ratios

```text
R_r(H) = Σ_{b≠0}|η_b(H)|^(2r) / ((p-1)(2r-1)!!σ^(2r))
```

decrease with `r` for the prize family `H = μ_{2^a}`.  R60 showed this is not true for all
multiplicative subgroups.  R61 maps the failure boundary across many subgroup orders.

Probe: `scripts/probes/probe_r61_order_boundary_monotonicity.py`.

## Result

Sweep of orders `6..58`, with exact coset spectra at `p ≈ order^4`:

```text
tested=53 failures=7
failure orders: 18 24 30 36 42 48 54
```

Targeted extension:

```text
order 60: fail R2=0.9832 < R3=1.0035, maxR=2.5259
order 66: fail R2=0.9848 < R3=0.9913, maxR=1.7199
order 72: fail R2=0.9861 < R3=0.9923, maxR=2.2008
order 78: fail R2=0.9871 < R3=0.9930, maxR=1.7144
order 84: fail R2=0.9881 < R3=0.9936, maxR=1.5065
```

Observed boundary:

* Pure 2-power orders tested: monotone.
* Odd orders tested: monotone.
* Many even non-2-power orders not divisible by 3: monotone in this sweep (`10,14,20,22,26,28,34,38,40,44,46,50,52,56,58`).
* Multiples of `6` from `18` onward: monotonicity fails, often with super-Wick ratios.

## Verdict

The first visible obstruction is a **6-divisibility resonance**: a simultaneous antipodal
pairing (`2 | |H|`) plus cubic structure (`3 | |H|`) creates super-Wick normalized moments.

This strongly refines the proof target.  A dyadic proof of normalized monotonicity should be able
to point to the absence of 3-torsion/cubic substructure as load-bearing, not just to generic
multiplicativity or even symmetry.

Candidate theorem shape after R61:

```text
For 2-power subgroups μ_{2^a}, R_{r+1} ≤ R_r.
This fails for subgroups with a 6-resonance.
```

The counterexample family `|H| ∈ {18,24,30,36,42,48,54,60,...}` is now an adversarial test suite
for any attempted proof: if the proof also covers those orders, it is proving a false statement.
