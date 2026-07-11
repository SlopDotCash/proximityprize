# Issue #466/#505 G127: the moment-LP dual — a systematic no-go generator

Date: 2026-07-11 (UTC)

## Results (`Frontier/_G127MomentLPDual.lean`, 2 declarations, axiom-clean, 0 sorryAx)

- `moment_LP_dual` (Farkas transfer): if multipliers `lam` dominate a cost vector `c`
  columnwise (`c s ≤ Σ_m lam m·(r−s)_m` for all s ≤ r), then
  `Σ_s c s·depthFiber A r s ≤ Σ_m lam m·(r)_m²·#A^m·E_{r−m}(A)`.
  Row m = 0 included, so the dual is complete.
- `census_claim_refuted` (no-go schema): a claimed census lower bound
  `B ≤ Σ c_s·fiber_s` is refuted by any dominating multipliers with dual value < B.

## Use

Every proposed deep-sector counterexample family carries a cost vector supported below full
depth and a claimed mass B. Refuting it is now a mechanical search for multipliers plus
kernel arithmetic on lower-rung energies — no new combinatorics per candidate. This turns
the G124 LP into an industrial refutation tool for the swarm's counterexample lanes
(DISPROOF_LOG candidates, spike/interval hybrids, G102-style extremal families).

## Honest scope

Transfer schema only; generates no bound on the fully-disjoint sector (weight 0 in all rows
m ≥ 1; row 0 costs full E_r). CORE remains OPEN.
