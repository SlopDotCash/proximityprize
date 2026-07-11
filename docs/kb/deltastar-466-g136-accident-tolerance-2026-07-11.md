# Issue #466 G136 (part 3a): the accident tolerance pin — at most three

Date: 2026-07-11 (UTC). `Frontier/_G136AccidentTolerance.lean`, 3 declarations,
axiom-clean, 0 sorryAx.

## Results

- `anchor_iff_tolerance`: under the accident-law shape `E₂ = 3n²−3n + n·A`, the rung-2
  anchor `q·E₂ ≤ 3qn² + n⁴` is EQUIVALENT to `q·A ≤ 3q + n³` (exact ℕ iff, n ≥ 1).
- `accident_tolerance` / `production_accident_tolerance`: when `n³ < q` (production:
  2^90 < q ≈ 2^158), that is EQUIVALENT to `A ≤ 3`.

## Reading

Modulo the accident law (part 2, fully designed, numerics verified), **the production
rung-2 anchor says precisely: the certified prime admits at most THREE accidents** —
at most three solutions of a+b = c+1 in μ_{2^30} beyond the Mann families (part 1).
Expected number ≈ 2^{-68}. The wall statement at rung 2 is now a finite, sharp,
zero-slack-interpreted arithmetic fact about one prime: not an estimate, an exact
tolerance. Parts 2 (the bijection + lawful count over ZMod p, design in memory/KB) and
the analogous higher-rung reductions remain.

CORE remains OPEN.
