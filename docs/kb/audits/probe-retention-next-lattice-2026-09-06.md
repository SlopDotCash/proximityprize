# Retention mapping: next-lattice perturbations — 2026-09-06

The full run of `scripts/probes/probe_rate_quarter_next_lattice_perturbations.py`
passes using Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0. It checks the
original received stack and twelve single-coordinate increments over F_97,
on the smooth 32-point domain, dimension eight and agreement threshold 18.

Three perturbations have one MCA-bad scalar and a maximum list size of one:
`u1[2]+=1`, `u0[12]+=1`, and `u0[16]+=1`. Every other case has empty lists.
Thus all thirteen tested stacks remain below the miniature budget of 32.
This does not classify other perturbations, all received stacks, or the
production parameters.

The imported GS helper uses 33 monomials of weighted degree at most 17
against 32 interpolation constraints. It extracts every polynomial root
of the resulting polynomial of Y-degree at most two by exact finite-field
factorization, then checks agreement and the no-joint condition. The
factor-extraction completeness argument, not merely verification of returned
candidates, is what supports the per-stack census. The helper and its
arithmetic path were source-reviewed; no independent decoder or Lean
recompilation is claimed.

The initial system-Python run stopped before computation because SymPy was
missing. The successful replay used an isolated environment; its deprecation
warning did not affect the result. The companion JSON records versions,
source/helper hashes, and all thirteen results. No source change was needed.

This source advances the original unreferenced cohort to 50 of 92 reviewed,
leaving 42. It remains retained.
