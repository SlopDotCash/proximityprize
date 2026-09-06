# Retention mapping: AJT13 centered moment — 2026-09-06

`scripts/probes/probe_ajt13_centered_tensor.py` separates two exact rational
centered-moment cells from four floating-point exponent analogues and four
floating-point CRT minor calculations.

The exact cells use integer convolution to count zero-sum tuples of subgroup
elements through length 14, then apply the stated orthogonality/moment formula
with rational arithmetic. At (n,m,q)=(32,98,3137), the normalized ratio is about
138535.54: above 13!!=135135 and below 2^18. At (256,52,13313), it is about
313471.77, above both constants. The companion JSON retains the exact fractions
and zero counts. These are finite cells outside the production thin regime;
they do not settle the production bound or independently formalize the
character-orthogonality identity used by the calculation.

The four exponent analogues use complex roots and floating-point powers for
n=2,4,8,16. Their increasing normalized coefficients do not establish a limit,
an asymptotic scaling law, or a production bound. The CRT computations find
large numerical minors at q=13,97,241,337, but supply no certified rounding-error
bounds. In particular, agreement within 1e-12 with the displayed q=13 expression
is not an exact symbolic proof of that expression.

The producer's reporting is corrected to preserve those distinctions. Its
arithmetic helpers are unchanged. Full replay and comparison evidence is
recorded in the companion JSON; no Lean compilation is claimed.

This source is one member of the original unreferenced cohort. With this audit,
49 of 92 are reviewed and 43 remain. The source is retained.
