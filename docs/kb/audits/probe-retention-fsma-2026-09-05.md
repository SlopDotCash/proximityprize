# Retention mapping: FSMA pair-mass bounds — 2026-09-05

The full default replay of `scripts/probes/probe_fsma_second_moment_pair_partition.py`
passed before and after correcting its interpretation labels. The adjacent JSON
records the source hash and output; arithmetic output is unchanged. This maps
one original artifact: 28 of 92 mapped, 64 remaining. No artifacts are deleted.

At the fixed P1 parameters N=2³⁰, K=2²⁸, T=592794966, the script uses exact
integer arithmetic and rational fractions for Plotkin caps and binary-search
thresholds. Decimal displays are approximate. Threshold assertions check the
scalar inequality on both sides; they do not construct set systems attaining it.
The old output label claiming t−1 was satisfiable has therefore been replaced
with a statement that the scalar threshold flips.

The rank-wise upper-bound calculation allows 108 ranks with at least ten points.
Its summed bound is 1156549403505116562, above the required pair mass
1152921505680588800. This does not prove that all rank maxima are jointly
attainable, or that a qualifying geometric configuration exists. The output now
states that the upper bound reaches the required mass, rather than calling the
channel sufficient. The finite ladder leaves the number of smaller lines
unbounded by this calculation; abstract pair assignments are not geometric
witnesses. These limitations replace the former unconditional barrier wording.

The displayed high-core threshold 721420286 exceeds T−2=592794964. This is an
arithmetic obstruction to applying that specified condition in the stated range,
not a general impossibility theorem. The referenced Lean companion was not
recompiled in this audit, and production completion remains open in issue #164.
