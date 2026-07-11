# δ* #466 — W15: the support-ladder floor for the mcaEvent-vocabulary safe large-zero branch (2026-07-10)

Lane: `ll:low-profile-fiber` (successor of W9). File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_W15LargeZeroMcaEventFloor.lean`
(axiom-clean, 11/11 `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
`pg-iterate` 7s).

## 0. Where this sits

`LineListMCAWeld.lean` reduces `δ ≤ mcaDeltaStar(RS, ε*)` to three branch budgets; W9
(`_W9LowProfilePencilSaturation.lean`) refuted the entire `lineBadScalars`-vocabulary safe
large-zero branch (`hsafe`/`hlowFiber`/mid-band/strata: root pencil forces every budget
`≥ |F|`) and named the sole survivor: the weld's ORIGINAL `hlow` hypothesis in
`mcaDeltaStar_ge_of_farLineListBudgeted`, phrased on the **`mcaEvent` filter**, where the
pencil produces only `1 + |W| ≤ 3` events (the joint pair `(0, e)` explains every pencil
scalar). The open sharp rung: the TRUE `mcaEvent` bad-scalar count on zero-direction-safe,
large-zero (`≥ a` zero coordinates) lines — `O(1)` or growing?

## 1. Verdict

**Growing: unconditional floor `n − a`.** Pencil scale (`O(1)`) is refuted; any budget of
the weld's `hlow` shape satisfies `B_near ≥ n − a`, at every shape `1 ≤ k`, `k + 1 ≤ a ≤ n`,
`(1 − δ)·n ≤ a`, over every field and injective domain.

## 2. The support ladder

Fix `Z ⊆ [n]`, `|Z| = a`, marked `z₀ ∈ Z`.

* direction `u₁ = 1` off `Z`, `0` on `Z` (zero set exactly `Z`: large-zero, not
  support-eligible);
* offset `u₀ = 0` on `Z ∖ {z₀}`, `1` at `z₀`, `−dom(i)` at each support point `i ∉ Z`.

For every support point `i`, the scalar `γ = dom(i)` fires `mcaEvent` with witness
`S = (Z ∖ {z₀}) ∪ {i}` (size `a`):

* the **zero codeword** lies on the line over `S` (`0 = 0 + γ·0` on `Z ∖ {z₀}`;
  `0 = −dom(i) + dom(i)·1` at `i`);
* **no joint pair**: a pair's direction component `v₁` must equal `u₁` on `S`, i.e. vanish
  on the `a − 1 ≥ k` points of `Z ∖ {z₀}` — so `v₁ = 0` by RS degree — yet equal `1` at
  `i`. The escape hatch that neutralized the W9 pencil (`mcaEvent_false_of_direction_mem`
  shape) is closed at every rung.

Safety (`ZeroDirectionSafeLine`): a codeword agreeing with `u₀` on `≥ a` points of `Z`
agrees on all of `Z` (`|Z| = a`), vanishes on `Z ∖ {z₀}` (`a − 1 ≥ k` points ⇒ it is `0`),
then fails at `z₀` where `u₀ = 1`. The `n − a` scalars `{dom(i) : i ∉ Z}` are distinct
(`dom` is an embedding).

## 3. Headlines (all in the W15 file)

1. `ladder_mcaEvent`, `ladder_mcaEvent_filter_card_ge` — the construction; count `≥ n − a`.
2. `weld_hlow_forces_n_sub_a` — the weld's `hlow` forces `B_near ≥ n − a`.
3. `safe_mcaEvent_budget_forces_n_sub_a` — the floor lives on the SAFE
   (`¬SupportEligible ∧ ZeroDirectionSafeLine`) class, exactly where W9 left the question.
4. `weld_budget_forces_epsilon_ge_n_sub_a_div_q` — every weld instantiation certifies at
   best `ε* ≥ (n − a)/q`.
5. `pencilScale_budget_refuted_rateQuarter` — rate-quarter shape `n = 16, a = 9`: floor
   `7 > 3`; the W9 probe's pencil count is not the class truth.

## 4. Honesty — what survives, and the new two-sided obligation

* **This is a linear-in-`n` floor, NOT a `q`-saturation.** In sharp contrast to W9's
  refutation, `ε* ≥ (n − a)/q` is exactly the BCIKS-shaped error regime the line-list route
  *targets* (`ε ~ n/q`). The `mcaEvent`-vocabulary safe branch REMAINS ALIVE.
* The production obligation is now two-sided: **lower bound `≥ n − a` CLOSED (this file);
  upper bound `B_near ≤ C·n` OPEN** — that upper bound is the live next rung of the lane.
* The ladder cannot go superlinear by itself: its base codeword is pinned by `u₀` on
  `a − 1 ≥ k` shared points, so one scalar per support point. Whether witnesses with
  `|S ∩ Z| < k` (freeing the base codeword) can push the floor to `ω(n)` — which WOULD
  kill the route at BCIKS shape — is genuinely undecided and is the natural refutation
  target for the next session.
* Needs `k + 1 ≤ a` (all of the sub-Johnson window) and `a ≤ n − 1` for non-vacuity; at
  `a = n` the floor is `0`, as it must be.

## 5. Next targets

1. (Upper bound) Prove `B_near ≤ C·n` on the safe class in the `mcaEvent` vocabulary —
   would complete the safe branch of the weld at BCIKS shape.
2. (Refutation) Multi-base ladders with `|S ∩ Z| < k`: search for `ω(n)` safe-line
   mcaEvent counts (deterministic probe warranted before Lean work).
3. Either outcome should be recorded against the weld's assembled consumers
   (`mcaDeltaStar_ge_of_farLineListBudgeted*`), whose `hunsafe` branch has the same
   vocabulary and likely admits the same ladder floor (the ladder line is safe, so it does
   not touch `hunsafe`; an unsafe-class analogue is untested).
