# Issue #466 G134: the production crossover pin + anchor-zone honesty audit

Date: 2026-07-11 (UTC). `Frontier/_G134ProductionCrossoverPin.lean`, 3 declarations,
axiom-clean, 0 sorryAx.

## Results

- `crossover_wick_side` / `crossover_dc_side`: at production (n = 2^30, 2^158 ≤ q ≤ 2^160),
  the DC-shape budget regime flips between rungs 5 and 6 — "the bump is at rungs 5–6" is now
  a kernel fact, not a heuristic.
- `sidon_threshold_fails_at_production`: the in-tree rung-2 anchor
  (`dcEnergyBound_two_rootsOfUnity`) requires `12^φ(2^30) = 12^(2^29) < p²`, and
  `2^320 < 2^(2^29)` — the threshold fails astronomically at production size.

## Honesty correction

Prior comments in this campaign (including mine) cited "the rung-2 anchor exists in-tree"
as if it covered production. It does NOT: it applies at the Sidon threshold (p enormous
relative to n) only. **All production anchors t = 2..10 of the G133 tower are OPEN.**
The heuristic picture stays favorable (at production, expected nontrivial quadruples
n³/p ≈ 2^-68 ≪ 1, so E_2 = 3n²−3n exactly is the expected truth), but proving any
production anchor is BGK-face work — consistent with the ON-BGK doctrine.

CORE remains OPEN.
