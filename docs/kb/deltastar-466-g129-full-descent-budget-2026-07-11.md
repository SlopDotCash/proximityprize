# Issue #466 G129 (part 1): the conditional full-descent budget

Date: 2026-07-11 (UTC)

## Results (`Frontier/_G129FullDescentBudget.lean`, 3 declarations, axiom-clean, 0 sorryAx)

- `shallow_descent_sharp`: depths 0..101 of the descent overhead bounded by the explicit
  two-term head (110!-term + 2·(110)_9²·n^210-term), any q ≤ 2^160 — trivial energies only.
- `production_gate_four` (kernel): 4·(shallow head) + 4·(deepTerm 102 + … + deepTerm 109)
  ≤ n^220, where deepTerm s carries the DC-shape value q·Wick_s + n^{2s}. Headroom ≈ 2^14.
- `production_full_descent_budget`: given DC-shape bounds `q·E_s ≤ q·Wick_s + n^{2s}` at
  rungs s = 102..109 ONLY, the FULL 110-depth production descent overhead satisfies
  `4·q·overhead ≤ n^220` — a quarter of the DC mass, leaving three quarters for the
  disjoint census in the G126 gate.

## Tower step (part 2, open)

DCEnergyBound at rung 110 ⟸ rung-110 disjoint census (vs 3/4 of the DC mass + Wick) + DC
at the eight predecessor rungs 102..109. Iterating per rung and pinning the low-rung
crossover would reduce the whole DC hierarchy at a certified prime to the disjoint-census
family. The split point matters: with trivial energies the s = 102 term alone is ≈ 0.4·n^220
(4× version fails); with its DC value it is ≈ 10^-5·n^220.

## Honest scope

Conditional on the eight predecessor DC bounds; no claim they hold. CORE remains OPEN.
