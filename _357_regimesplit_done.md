## LANDED: the regime-split weld (`KKH26RegimeSplit.lean`, axiom-clean, COMMIT_HASH)

As announced (the red-team x2 + lane-claim comment): the frontier between the Johnson lane and the open core is now **enforced by types**, not comment-thread discipline.

What landed (all `[propext, Classical.choice, Quot.sound]`, 0 sorry, full strict build):

- **`powDomain` + `evalCode_eq_reedSolomon`** — the first in-tree identification of the KKH26 ceiling family `evalCode g n d` with `ReedSolomon.code (powDomain g) (d+1)` on the `i ↦ gⁱ` domain. The ceiling construction and the entire Hab25/BCIKS20 Johnson cone now speak the same language.
- **`RegimeIIIGoodness`** — THE named open core: `ε_mca ≤ ε*` on `[δJ, 1 − r/2^μ)`. With `δJ = gs_johnson`, this is exactly the strictly-above-Johnson band — the 25-year wall, now a single typed Prop.
- **`interiorCeiling_of_below_and_regimeIII`** — the case-split decomposition of `InteriorCeiling`.
- **`epsMCA_evalCode_le_of_johnsonDischarge`** — `JohnsonDischargeStatement` + the budget inequality ⟹ goodness at every radius below `gs_johnson (d+1) n m₀`, transported to the KKH26 code via the bridge.
- **`kkh26_deltaStar_pin_of_johnsonDischarge_and_regimeIII`** — **the weld**: `JohnsonDischargeStatement ⊕ RegimeIIIGoodness ⊕ budget arithmetic ⟹ mcaDeltaStar(evalCode g n ((r−2)m), ε*) = 1 − r/2^μ` exactly.
- **`gs_johnson_lt_jump`** — the formal guard: under `r²·m < 2^μ·k` (every live parameter point), `gs_johnson < 1 − r/2^μ` — regime III is provably nonempty, so no instantiation of the weld can degenerate it away.

**Synergy with round 24:** the weld's `hbudget` hypothesis is exactly what `ProductionJohnsonBudget.johnsonBoundReal_le_production` + `production_johnson_reach` discharge at production parameters (rate ≥ 1/2, `ε* = 2^-128`, `q ≥ 2^192`). Composing: when the Johnson lane's `CellPackageSupply` closes (finding-14 repair pending), the **entire remaining hypothesis of the exact δ* pin is `RegimeIIIGoodness` alone** — one Prop, one band, the honest wall.

**Follow-up noted (not claimed):** instantiating the weld at the Parseval-opened `s = 64` rows at `ε* = 2^-128` needs a pin variant with the sharpened prime threshold — the current `kkh26_deltaStar_pin_of_interior_ceiling` carries the worst-case resultant hypothesis `(2^μ)^{2^{μ−1}} < p` (≈ 2^448 at μ = 7), which production fields don't meet; the Parseval-route lower bound (`KKH26ParsevalThreshold`) is the natural supplier.

**Honest scope:** the weld does not move the wall; it makes the wall un-skippable.
