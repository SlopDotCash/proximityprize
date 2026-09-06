# I031 quotient-floor audit (#444, 2026-06-15)

## Status

`I031` survives this audit.  The quotient-collapse leg is now Lean-packaged, and the
small direct probe finds no counterexample to the bounded floor-constant prediction.
This does **not** prove the remaining deterministic-to-Gaussian sup comparison,
but a seeded matched-Gaussian simulation does not refute it.

## Lean bricks

- `Research/ProximityPrize/Frontier/PeriodOrbitQuotientReduction.lean`
  validates the representative-cover consumer:
  representative bounds on a coset cover imply all nonzero-frequency period bounds.
- `Research/ProximityPrize/Frontier/_I031OrbitQuotient.lean`
  validates the exact image/max quotient collapse:
  the nonzero period-norm spectrum equals the representative period-norm spectrum.

Both compile with `scripts/pg-iterate.sh`; axiom audits report only the standard
`[propext]` dependency for these statements.

## Probe

Command:

```bash
python3 scripts/probes/probe_i031_quotient_floor_audit.py
```

Output:

```text
I031 quotient-floor audit
direct exact cosets; proper subgroup only (m=(p-1)/n > 1)
    n  beta          p        m   coset spread    M/sqrt(n log m)   M/E sup G    m/(p-1)
   16  2.40        881       55      3.557e-15              1.265       1.255  6.250e-02
   32  2.35       3457      108      1.066e-14              1.472       1.423  3.125e-02
   64  2.25      11777      184      1.438e-14              1.334       1.279  1.562e-02
  128  2.10      26881      210      3.557e-14              1.349       1.313  7.812e-03
verdict: coset constancy holds to roundoff; floor constants in [1.265, 1.472].
transfer audit: deterministic/Gaussian sup ratios in [1.255, 1.423] with a fixed seed.
status: I031 survives this audit; the remaining gap is proving the bounded transfer.
```

## Interpretation

The quotient entropy collapse is closed: the period process is constant on
`mu_n`-dilation orbits, so the supremum can be checked on `m = (p-1)/n` coset
representatives.  The probe confirms exact coset constancy to floating roundoff
and keeps `M / sqrt(n log m)` bounded on modest proper-subgroup instances.
The seeded matched-Gaussian comparison also stays bounded:
`M / E sup |G_b| in [1.255, 1.423]`.

The open step remains sharply localized:

> prove a bounded-constant deterministic-to-Gaussian sup comparison for the
> cyclotomic quotient process indexed by `F_p^*/mu_n`.

This is not the raw BGK moment wall, not a Wasserstein fixed-order route, and not a
second-moment certificate.  It is the current best I031 handle after quotienting.
