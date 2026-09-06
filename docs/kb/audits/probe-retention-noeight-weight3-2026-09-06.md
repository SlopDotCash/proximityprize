# Nine-coordinate syndrome probe review

Retain `scripts/probes/probe_noeight_n9k4_weight3_lines.py`. Its complete default million-line seeded sample finds a line with 13 proper weight-three syndrome representatives over F17, exceeding the proposed bare bound of twelve. Exit 1 is the program's explicit counterexample result, not an execution failure. The companion JSON preserves every printed support, coefficient, and annihilator witness.

The certificate routine reconstructs each syndrome by exact modular arithmetic and finds a support annihilator that is nonzero on the direction. This supports the bare syndrome counterexample, not the source-root-coupled production residual. The source-root audit enumerates 560² possible lifts constrained at two witnessed scalars; its result is restricted to the selected witness representatives.

This review fixes two input-dependent errors: the seven-point source must be the complement of the configured nine-point domain, and the audit must interpolate using two available distinct witnessed scalars rather than assume 0 and 1 are present. Search sizes must be positive and domain exponents distinct and in range. Regression tests exercise a rotated domain, reparameterized scalar line, removal of scalars 0 and 1, and invalid inputs; both tests pass.

The original unreferenced-source review advances the corrected aggregate to 75 of 92, leaving 17. No production theorem is discharged.
