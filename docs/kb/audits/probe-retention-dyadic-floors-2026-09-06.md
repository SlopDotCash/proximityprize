# Retention mapping: dyadic partition floors — 2026-09-06

Complete producer replays map two retained archives:

- `scripts/probes/_out_316_dyadic_wall_floor_depth3.txt` is byte-identical to the full G316 replay.
- `scripts/probes/_out_324_dyadic_wall_floor_depth4.txt` is byte-identical to the original G324 replay. The corrected producer changes only two summary lines; every numerical row and witness is unchanged. The historical archive is retained unchanged.

Both programs enumerate feasible nonnegative integer partitions for all 198
values m=2..199 and compare their maxima with the respective formulas. G316
checks parts of sizes 1..3 and G324 sizes 1..4, holding the class-count cap
at m and weighted partition sum at 2m-1. These computations validate those
finite integer optimization problems, not the extension of the underlying
cyclotomic model to higher depth.

G324's output incorrectly claimed strict improvement over depth three at
m=2. Both maxima are 9 there; strict improvement starts at m=3. The code
already checks this boundary correctly. Its header also called a 198-case
replay a universal computational proof and described three nested loops
as quadratic. The correction states the finite scope, the equality case,
and the cubic worst-case enumeration cost. No numerical code changed.

These two archives advance the original unreferenced cohort from 44 to
46 of 92, leaving 46. Both source programs already had direct Lean references
and do not separately increment that cohort. No artifact is deleted by
this audit. The companion JSON records full output, hashes, and the exact
archive difference. This audit does not recompile the historical Lean
certificates or establish a universal bound or production prize theorem.
