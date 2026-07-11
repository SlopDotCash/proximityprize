# Issue #466 G128: the production descent budget — unconditional through depth 102

Date: 2026-07-11 (UTC)

Quantifies the G126 gate's descent charge at production shape (#G, r) = (2^30, 110),
q ≤ 2^160 (both certified prize primes qualify).

## Results (`Frontier/_G128ProductionDescentBudget.lean`, 4 declarations, axiom-clean, 0 sorryAx)

- `descB_halving`: the trivial-energy descent series `B k = q·(110)_k²·n^{219−k}` at least
  halves per step (`2·(110−k)² ≤ 2^30`).
- `descB_tail`: geometric — the whole tail is at most `2·B(head)`.
- `production_gate` (kernel): `2^160·(110!)²·n^110 + 2·(2^160·(110)_8²·n^211) ≤ n^220`
  (≈ 2^3 headroom).
- `production_shallow_descent_within_DC`: with ONLY the trivial in-tree energy bounds
  (`E_0 = 1`, `E_s ≤ n^{2s−1}`), the descent overhead over depths 0..102 fits inside the DC
  mass `n^{220}` outright, for any `q ≤ 2^160`.

## Consequence

In the disjoint-census gate at production scale, only the SEVEN deepest sub-full depths
(s = 103..109) require true (conditional) lower-rung energy input — 103 of the 110 descent
depths are free with zero analytic input. The production obligation is now: the
fully-disjoint census `depthFiber G 110 110` plus seven near-full-depth energies
`E_103..E_109`, against the Wick-plus-DC budget.

## Honest scope

Nothing here bounds the disjoint census or the seven deep energies — that is the wall.
CORE remains OPEN.
