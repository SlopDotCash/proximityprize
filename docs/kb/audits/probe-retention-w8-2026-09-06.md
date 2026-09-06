# W8 multicore probe review

Retain `scripts/probes/probe_w8_multicore_ladder.py` as arithmetic and construction-search evidence. Its complete current run exited 0 and reached ALL CHECKS PASS. The full output and source hash are recorded in the companion JSON.

The s=64 searches find 66 and 130 distinct base coset labels for the two configured large moduli. The printed lifted counts multiply these by m=2²⁴, giving 1107296256 and 2181038080. Base rank and distinctness calculations use modular arithmetic, while fresh-point identities and properness are spot-checked. This review has not independently certified primality of the two large moduli or verified every lifted point; these are not newly compiled Lean certificates.

The F4001 toy stage enumerates every support of sizes 11 and 12, solves its scalar agreement equations, excludes joint supports, and checks inclusion of the constructed scalar set. Its scope is this fixed toy pair. The dyadic feasibility ladder uses the exact integer formula tested against 5000 exhaustive small cases in [the ladder audit](w8-ladder-formula-2026-09-06.md).

The source's optimized-family and prize-bracket narrative must be read with those limits: a finite probe pass does not discharge a production theorem or establish optimality over constructions outside its stated family. The original unreferenced-source review advances the corrected aggregate to 72 of 92, with 20 remaining.
