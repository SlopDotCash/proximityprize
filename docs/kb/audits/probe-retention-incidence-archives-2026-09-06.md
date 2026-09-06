# Retention mapping: incidence archives — 2026-09-06

Three complete producer replays map these retained archives:

- `scripts/probes/_out_322_overdet_incidence_max_extended.txt`: byte-identical replay of `g322_overdet_incidence_max_extended.py`.
- `scripts/probes/_out_325_overdet_incidence_max_m26_50.txt`: byte-identical replay of `g325_overdet_incidence_max_m26_50.py`.
- `scripts/probes/_out_326_overdet_incidence_max_stronger_decoupling.txt`: replay of `g326_overdet_incidence_max_stronger_decoupling.py` differs only in the corrected final summary word, “quadratically” to “cubically”. Every numerical value and other byte matches. The historical archive is retained unchanged.

These three archives advance the original unreferenced cohort to 44 of 92
reviewed, with 48 remaining. The G326 source was already counted separately;
the other two producers have direct references and do not increment this cohort.

G322 compares the equivalent cubic and binomial formulas at m=2..25, checks
bulk and 4m bounds on that range, checks the 8m bound at m=3..25, and checks
the exact discrete derivative and monotonicity at m=1..24. Its expected-value
pin loops cover m=2..20 only: the declared m=21..25 dictionary is not used by
a pin loop. Those final five cells receive formula-agreement checks, not a
comparison against their stored expected values.

G325 checks all 49 expected values at m=2..50, plus bulk and 4m bounds on
that range, the 8m bound at m=3..50, and monotonicity and the exact discrete
derivative at m=1..49. G326's four tight bounds and separate non-tight 8m
bound are detailed in `probe-retention-g326-2026-09-06.md`.

All computations use exact integers. Agreement between algebraically
equivalent formulas does not independently validate the incidence model.
These finite replays neither prove universal bounds nor recompile the Lean
certificates mentioned in historical headers. No prize closure is claimed.
The companion JSON preserves source/archive hashes, complete output, and
precise comparison results.
