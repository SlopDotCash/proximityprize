# Retention mapping: FSMF predecessor miniature — 2026-09-06

The full run of `scripts/probes/probe_fsmf_predecessor_miniature_census.py`
passes and reproduces `_out_fsmf_miniature_census.txt` byte-for-byte, using
Python 3.14.6 and NumPy 2.4.4.

The F_97 cross-check reproduces 36 bad scalars at agreement 17 and zero at
18. The principal miniature uses F_193, n=64, dimension 16 and agreement
threshold 36. The three constructed stacks have bad counts 58, 50 and 19.
The eight listed coordinate perturbations of the first stack have counts
0,29,29,58,0,29,58,0. None exceeds the miniature budget of 64.

For each fixed stack the engine enumerates every field scalar. Its
multiplicity-two GS interpolation polynomial has weighted degree 2t-1,
with more monomials than constraints. Exact modular nullspace verification,
Roth–Ruckenstein root enumeration, direct agreement counting and received-row
interpolation implement the list and no-joint checks. The zero-polynomial
exception aborts rather than silently truncating the root search. The code
and completeness argument were source-reviewed; this is not an independent
implementation or a new Lean compilation.

The miniature has m=4, whereas the cited production-facing cover lemma
requires m>=8. Its finite stacks and perturbations do not establish the
all-stack predecessor bound, nor a production counterexample. The complete
archive, source hash, runtime and summary are preserved in the companion JSON.

Both the source and archive belonged to the original unreferenced cohort.
This advances that cohort to 53 of 92 reviewed, leaving 39. They remain
retained; the earlier removal of the redundant G104 printer is unchanged.
