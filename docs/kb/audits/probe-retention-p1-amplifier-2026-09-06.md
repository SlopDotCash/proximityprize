# Retention mapping: saturated P1 common factor — 2026-09-06

The complete default run of
`scripts/probes/probe_rate_quarter_p1_common_factor_amplifier.py` passes.
It verifies the fixed modular generator-order checks, cubic-locator identity,
two explicit hole rows, six distinct unsafe coset identifiers, pointwise
row identities, and the degree/count arithmetic at maximal amplification.

The agreement threshold is 592794965 and the radius numerator is 480946859
at n=2^30. Exact rational comparison confirms radius = 43/96 + 1/(3n).
These parameters agree with the saturated case in the separately replayed
common-factor trade probe. The construction's arithmetic ledger gives n+2
bad labels. The companion JSON preserves every returned constant and the
source hash.

This is a fixed arithmetic/coset certificate, not an enumeration of the
billion-point domain. The abstract fibre-cardinality and construction-to-MCA
arguments are not proved by executing this script. The fixed modulus's
primality was not independently certified here, and no Lean recompilation
or production threshold equality is claimed.

This source advances the original unreferenced cohort to 54 of 92 reviewed,
leaving 38. It remains retained.
