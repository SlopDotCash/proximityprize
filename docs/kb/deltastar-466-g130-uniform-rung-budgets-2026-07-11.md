# Issue #466 G130 (= G129 part 2b core): uniform per-rung budget lemmas

Date: 2026-07-11 (UTC)

The tower induction needs G128/G129-style budgets at every rung t ≤ 110. One hundred kernel
gates are infeasible; G130 replaces them with four uniform lemmas (clean inductions, huge
slack), all axiom-clean:

- `factorial_sq_le`: `2^163·(t!)² ≤ 2^(30t)` for 7 ≤ t ≤ 110 (step `(t+1)² ≤ 2^30`).
- `shallow_head_gate`: `16·2^160·(110)_9² ≤ 2^300` — one gate for the geometric shallow tail
  at every rung, via the new `descFactorial_mono_base` ((t)_9 ≤ (110)_9).
- `deep_dc_gate`: `64·(110)_k² ≤ 2^(30k)`, 1 ≤ k ≤ 8.
- `deep_wick_le`: `2^166·(110)_8²·(2t−1)!! ≤ 2^(30t)` for 11 ≤ t ≤ 110 (step `2t+1 ≤ 2^8`;
  base t = 11 — t = 10 provably fails with the crude (110)_8 bound, calibrated numerically).

## Remaining assembly (part 2b sequel)

Per-rung generalization of `shallow_descent_sharp` / `production_full_descent_budget` /
`dcEnergyBound_*_of_census_and_predecessors` consuming these four lemmas, then strong
induction over rungs (descending 8 per step) from 110 down to the crossover t₀ = 11:
the whole DC hierarchy at a certified prime from {disjoint censuses, rungs 11..110} +
low-rung anchors (rung-2 anchor exists in-tree; 3..10 need theirs).

## Honest scope

Arithmetic infrastructure; nothing analytic. CORE remains OPEN.
