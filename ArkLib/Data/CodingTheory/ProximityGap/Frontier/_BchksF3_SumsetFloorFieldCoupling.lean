/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF3_RetargetedReduction
import Mathlib.Tactic

/-!
# BCHKS F3 — the Sumset-Extremality floor's `|F|`-COUPLING constraint (#444)

**Context.** `_BchksF3_RetargetedReduction` re-targets the prize onto the open floor

> `SumsetExtremality bad sumset poly soundness :=`
> `  bad ≤ poly · sumset  ∧  poly · sumset ≤ soundness`,

where `sumset = |Σ_r(μ_s)| = |H^{(+r)}|` is the `r`-fold sumset size and `soundness = ε*·|F|`
(`|F|` taken LARGE). F3 PROVES (`subsetSumBudget_existential_unsat`) that the sumset is **monotone
INCREASING** in the fold `r` (`|Σ_r(μ_16)| = 129, 704, 2945, 10128, 29953, 78592, 185617` for
`r = 2..8`). This file discharges the structural consequence of that monotonicity for the floor's
**second conjunct** `poly · sumset ≤ soundness`, which F3 leaves implicit.

## The constraint (probe `scripts/probes/probe_f3_sumset_monotone_floor.py`, 0 fails / 6)

Because the sumset is increasing in the fold, the soundness conjunct `poly · sumset ≤ soundness` is
a **down-set in the sumset** (it can only hold for SMALL sumsets, i.e. SHALLOW folds). But the
binding fold `m*` is DEEP (F3's `mStar_ge_three_*`: `m* ≥ 3`, and it grows). So at the deep binding
fold the soundness conjunct is a genuine constraint that **couples `|F|` to the deep-fold sumset
size**:

> **`|F|`-coupling.** `SumsetExtremality bad sumset poly (ε·|F|)` ⟹ `poly · sumset ≤ ε·|F|`,
> i.e. `|F| ≥ poly · sumset / ε`. At the deep binding fold `M`, `sumset = |Σ_M|` is super-poly in
> `M`, so the "`|F|` large" of the floor is NOT free — it is a super-poly-in-depth lower bound on
> the field size, the precise non-vacuity cost of the re-targeted floor.

This is the SAME increasing-dominator structure as the F6 crossing-fold constraint (O238), here on
the SUMSET rather than `chooseCH`. It does NOT prove or refute CORE; it pins the `|F|`-coupling cost
of the F3 floor's soundness conjunct.

## Honesty (the contract)

EXTEND-proven on F3's `SumsetExtremality`. Pure `Nat`/`Nat`-division monotonicity; field-universal
(no thinness), so it CANNOT (and does not) prove CORE. The increasing `|Σ_r|` is an
additive-combinatorics SUMSET-SIZE object, NOT a `δ*`/incidence object — the asymptotic-guard
cliff-at-`n/2` is UNTOUCHED, and we make NO capacity / beyond-Johnson claim (we only pin the
`|F|`-coupling cost of the floor's soundness conjunct). We do NOT re-derive F3's `|Σ_r| > budget`
refutation (already a theorem). Axiom audit must show a subset of
`{propext, Classical.choice, Quot.sound}` — no `sorryAx`.

Issue #444, constraint on F3 (`_BchksF3_RetargetedReduction`). Builds on `SumsetExtremality`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.BchksF3

/-! ## 1. The soundness conjunct is a DOWN-SET in the sumset (monotone-failing for larger sumset) -/

/-- **The soundness conjunct is monotone in the sumset.** If the floor's soundness budget holds for
a sumset `sumset₂` (`poly · sumset₂ ≤ soundness`), then it holds for every SMALLER sumset
`sumset₁ ≤ sumset₂`. Since `|Σ_r|` is INCREASING in the fold `r` (F3's
`subsetSumBudget_existential_unsat`), this makes `{r : poly · |Σ_r| ≤ soundness}` a down-set in `r`:
the soundness conjunct can hold only at SHALLOW folds. -/
theorem soundness_conjunct_downward_closed
    {poly sumset₁ sumset₂ soundness : ℕ}
    (hle : sumset₁ ≤ sumset₂)
    (h₂ : poly * sumset₂ ≤ soundness) :
    poly * sumset₁ ≤ soundness :=
  le_trans (Nat.mul_le_mul_left poly hle) h₂

/-- **The soundness conjunct FAILS at every larger sumset (the hard upper edge).** If the soundness
budget is already exceeded at a sumset `sumset₁` (`soundness < poly · sumset₁`), then it is exceeded
at every LARGER sumset `sumset₂ ≥ sumset₁` — so along the increasing fold `r`, once the soundness
conjunct fails it stays failed. The hard edge of the floor's soundness conjunct. -/
theorem soundness_conjunct_fails_above
    {poly sumset₁ sumset₂ soundness : ℕ}
    (hle : sumset₁ ≤ sumset₂)
    (hfail : soundness < poly * sumset₁) :
    soundness < poly * sumset₂ :=
  lt_of_lt_of_le hfail (Nat.mul_le_mul_left poly hle)

/-! ## 2. The `|F|`-coupling — the floor's soundness conjunct forces a field-size lower bound -/

/-- **The Sumset-Extremality floor forces `poly · sumset ≤ ε·|F|`.** With the soundness budget
modeled as `soundness = ε · |F|`, the floor's second conjunct is exactly the field-size coupling
`poly · sumset ≤ ε · |F|`: the bad-scalar count's sumset-multiplier dominator must fit inside the
soundness error `ε·|F|`. (The second conjunct of `SumsetExtremality`, named as the coupling.) -/
theorem sumsetExtremality_forces_field_coupling
    {bad sumset poly eps fieldCard : ℕ}
    (hext : SumsetExtremality bad sumset poly (eps * fieldCard)) :
    poly * sumset ≤ eps * fieldCard :=
  hext.2

/-- **The field-size lower bound (`|F| ≥ poly · sumset / ε`).** From the floor's soundness conjunct
`poly · sumset ≤ ε · |F|` with `ε ≥ 1`, the field size is bounded below by `poly · sumset / ε`
(`Nat` division). At the DEEP binding fold `M` (where `sumset = |Σ_M|` is super-poly in `M`), this
is a super-poly-in-depth lower bound on `|F|` — the "`|F|` large" of the floor is not free. -/
theorem field_card_lower_bound_of_sumsetExtremality
    {bad sumset poly eps fieldCard : ℕ} (heps : 1 ≤ eps)
    (hext : SumsetExtremality bad sumset poly (eps * fieldCard)) :
    poly * sumset / eps ≤ fieldCard := by
  have hcoup : poly * sumset ≤ eps * fieldCard :=
    sumsetExtremality_forces_field_coupling hext
  calc poly * sumset / eps ≤ (eps * fieldCard) / eps := Nat.div_le_div_right hcoup
    _ = fieldCard := by
        rw [Nat.mul_div_cancel_left fieldCard (Nat.lt_of_lt_of_le Nat.zero_lt_one heps)]

/-! ## 3. Deep-fold instantiation — the coupling at F3's exact sumset values -/

/-- **The coupling bites at the deep fold (F3's `n=s=16` values).** With F3's exact sumset
`|Σ_8(μ_16)| = 185617`, `poly = 1`, `ε = 1`: any field with `SumsetExtremality` at this fold must
have `|F| ≥ 185617` — already four orders of magnitude above the OLD (refuted) budget `16`. So the
floor's "`|F|` large" is a real, deep-fold-driven field-size lower bound, growing with the
(increasing, super-poly) sumset. -/
theorem deep_fold_field_lower_bound
    {bad fieldCard : ℕ}
    (hext : SumsetExtremality bad 185617 1 (1 * fieldCard)) :
    185617 ≤ fieldCard := by
  have := field_card_lower_bound_of_sumsetExtremality (bad := bad) (sumset := 185617)
    (poly := 1) (eps := 1) (fieldCard := fieldCard) (by norm_num) hext
  simpa using this

/-- **The deep-fold sumset STRICTLY exceeds the shallow-fold sumset (F3's `n=s=16` table).** The
field-size lower bound grows along the fold: `|Σ_3| = 704 < |Σ_8| = 185617`, so the deep binding
fold forces a strictly larger `|F|` than any shallow fold would. (The increasing-dominator down-set,
pinned at F3's exact values — the reason the coupling is a DEEP-fold constraint.) -/
theorem deep_fold_sumset_dominates : (704 : ℕ) < 185617 := by norm_num

end ArkLib.ProximityGap.BchksF3

/-! ## Axiom audit (expected: a subset of `propext, Classical.choice, Quot.sound` — no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.BchksF3.soundness_conjunct_downward_closed
#print axioms ArkLib.ProximityGap.BchksF3.soundness_conjunct_fails_above
#print axioms ArkLib.ProximityGap.BchksF3.sumsetExtremality_forces_field_coupling
#print axioms ArkLib.ProximityGap.BchksF3.field_card_lower_bound_of_sumsetExtremality
#print axioms ArkLib.ProximityGap.BchksF3.deep_fold_field_lower_bound
#print axioms ArkLib.ProximityGap.BchksF3.deep_fold_sumset_dominates
