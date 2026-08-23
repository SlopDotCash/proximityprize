/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Log
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.OverdetVanishingCosetCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CosetUnionVanishingLower

/-!
# §6.4/6.5 — the vanishing supply UNCONDITIONALLY exceeds the budget at prize depth (#444)

`OverdetVanishingCosetCount.budget_exponent_lt_supply_exponent` proves `L < (2^L)/dyadicBlock r`
(the supply *exponent* `n/d` exceeds the budget exponent `L`, for `n = 2^L`), but for the
**closed-form VALUE** `V_r(n) = 2^{n/d}`, which it carries from Lam–Leung as the count.  And
`CosetUnionVanishingLower.card_le_vanishing_of_blockUnions` proves the **actual** vanishing count is
`≥ 2^{n/d}` (the lower direction, now a theorem).  This file COMBINES the two to make the
budget-vs-supply constraint **unconditional**:

> **`2^L < #{ S ⊆ μ_n : ∑_{x∈S} x = 0 }`**

at prize depth `r` (`n = 2^L`, `2L²+2L ≤ n`, `1 ≤ r ≤ L`), given only that `μ_n` has `n/dyadicBlock r`
pairwise-disjoint nonempty **zero-sum cosets** (true: cosets of the order-`dyadicBlock r` subgroup,
each `∑ = ζ^i·∑ d`-th roots `= 0`).  No carried Lam–Leung.

This removes the probe-carried hypothesis from the §6.4 m∗ growth-law constraint: the coset-union
vanishing supply super-exponentially exceeds the budget `q·ε* = 2^L` at the prize binding depth, so
the supply is **not** the binding constraint — and that is now a THEOREM about the genuine count, not
just its carried closed-form value.

## What is proved (axiom-clean)

- `two_pow_budget_lt_supply_value` — `2^L < 2^{(2^L)/dyadicBlock r}` (monotone-in-exponent lift of
  `budget_exponent_lt_supply_exponent`).
- `budget_lt_vanishing_card` — the headline: `2^L < #vanishing`, given the `n/d` zero-sum cosets.

## Scope / honesty (rule 3, rule 6)

CHAR-0, NOT thinness-essential, NOT a CORE closure.  It pins a SUPPLY/BUDGET inequality
(`V_r > q·ε*` at prize depth) unconditionally — confirming the coset-union supply is loose, NOT the
binding constraint.  This is a NEGATIVE/structural fact (the binding constraint lives elsewhere, the
under-det/BGK face per the §6 meta-analysis), not a CORE upper bound.  `M(μ_n) ≤ C√(n log m)` OPEN.

Issue #444, §6.4/6.5 (supply-vs-budget, unconditional).
-/

set_option linter.unusedVariables false

namespace ArkLib.ProximityGap.SupplyExceedsBudgetUnconditional

open ProximityGap.Frontier.OverdetVanishingCosetCount
open ArkLib.ProximityGap.CosetUnionVanishingLower

/-- **Budget value strictly below supply value.**  From `L < (2^L)/dyadicBlock r`
(`budget_exponent_lt_supply_exponent`), monotonicity of `2^·` gives `2^L < 2^{(2^L)/dyadicBlock r}`,
i.e. the budget `q·ε* = 2^L` is strictly below the coset-union supply value `V_r(n) = 2^{n/d}`. -/
theorem two_pow_budget_lt_supply_value
    (L r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) (hbig : 2 * L * L + 2 * L ≤ 2 ^ L) :
    2 ^ L < 2 ^ ((2 ^ L) / dyadicBlock r) :=
  Nat.pow_lt_pow_right (by decide)
    (budget_exponent_lt_supply_exponent L r hr hrL hbig)

/-- **The headline (unconditional): `2^L < #vanishing` at prize depth.**

Given `n = 2^L` partitioned into `p = n / dyadicBlock r` pairwise-disjoint nonempty zero-sum blocks
(the cosets of the order-`dyadicBlock r` subgroup of `μ_n`, each summing to `0`), the actual
vanishing count is `≥ 2^p = 2^{n/d}` (`card_le_vanishing_of_blockUnions`), which strictly exceeds the
budget `2^L` (`two_pow_budget_lt_supply_value`).  Hence the supply super-exponentially exceeds the
budget at the prize binding depth — UNCONDITIONALLY (no carried Lam–Leung). -/
theorem budget_lt_vanishing_card
    {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (L r : ℕ) (hr : 1 ≤ r) (hrL : r ≤ L) (hbig : 2 * L * L + 2 * L ≤ 2 ^ L)
    (block : Fin ((2 ^ L) / dyadicBlock r) → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (block i) (block j))
    (hne : ∀ i, (block i).Nonempty)
    (hzero : ∀ i, ∑ x ∈ block i, x = 0) :
    2 ^ L < (Finset.univ.filter (fun S : Finset G => ∑ x ∈ S, x = 0)).card := by
  calc 2 ^ L
      < 2 ^ ((2 ^ L) / dyadicBlock r) := two_pow_budget_lt_supply_value L r hr hrL hbig
    _ ≤ _ := card_le_vanishing_of_blockUnions block hdisj hne hzero

end ArkLib.ProximityGap.SupplyExceedsBudgetUnconditional

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SupplyExceedsBudgetUnconditional.two_pow_budget_lt_supply_value
#print axioms ArkLib.ProximityGap.SupplyExceedsBudgetUnconditional.budget_lt_vanishing_card
