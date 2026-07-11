# Issue #466 G132: per-rung budget assembly

Date: 2026-07-11 (UTC)

Assembles G130's uniform gates + G131's series into the per-rung budgets, for every rung
11 ≤ t ≤ 110 and q ≤ 2^160 (`Frontier/_G132PerRungBudgetAssembly.lean`, 5 declarations,
axiom-clean, 0 sorryAx):

- `descFactorial_mono_len`, `doubleFactorial_odd_mono`: two small monotonicity bricks
  (upstreamable).
- `perRung_shallow_budget`: trivial energies only — shallow descent (depths 0..t−9) fits a
  QUARTER of the rung-t DC mass: `4·q·Σ_{s<t−8} (t)_{t−s}²·n^{t−s}·E_s ≤ n^{2t}`.
- `perRung_deep_budget`: with DC-shape bounds at the eight predecessor rungs, the deep
  descent (depths t−8..t−1) fits a quarter as well (64×-split; both G130 gates are exact
  at 64).
- `perRung_full_budget`: together `2·q·(full rung-t overhead) ≤ n^{2t}` — half the DC mass,
  leaving half for the disjoint census.

## Tower status

Arithmetic + budget layers now COMPLETE for all rungs 11..110. Remaining: the per-rung
census gate (G126 shape at rung t, consuming perRung_full_budget with the ½/½ split) and
the strong induction over rungs (descend 8 per step, base t₀ = 11, low-rung anchors ≤ 10).
After that: the whole DC hierarchy at a certified prime ⟸ the disjoint-census family.

CORE remains OPEN — the census family is the wall.
