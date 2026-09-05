# Retention mapping: W15 window budget — 2026-09-05

The retained `scripts/probes/probe_w15_window_rational_linear_refute.py` completed
with exit zero. Its value-class census agrees with its independent subset census
for all 31 scalars. The exact output is stored in the adjacent JSON record.
This maps one more original unreferenced artifact: 24 of 92 mapped, 68 remaining.

For n=10, k=1, w=7 over F31, the bad scalars are
0, 2, 5, 6, 10, 11, 16, 18, 20, 22, 26, 29, 30: thirteen, not twelve.
The two rows each agree with a constant on three coordinates; each error set
has size seven. The rational agreement threshold is exactly three.
The parameters satisfy w+k≤n and w+3≤n, but 2w+k=15>10.

`WBPencilLinearBudget.lean` defines `WindowRationalLinear` without a below-UDR
guard. Its consumers explicitly assume that residual, so this finite example
challenges an unconditional reading of the residual, not the validity of those
conditional implications. The stale source docstring and probe count are
corrected; no theorem statement or proof is changed. This audit is an exact
Python computation, not a newly kernel-checked refutation or a prize proof.
