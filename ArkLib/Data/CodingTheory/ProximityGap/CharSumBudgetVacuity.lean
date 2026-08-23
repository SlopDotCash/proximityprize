/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CharSumDeltaStarBridge

/-!
# The char-sum -> incidence budget is VACUOUS at the prize budget (#444)

`CharSumDeltaStarBridge.le_mcaDeltaStar_of_charSumBound` packages the only currently-available
`M -> epsMCA` route through the **naive** per-line incidence budget
`charSumIncidenceBudget G B = ⌈|G| + q·B⌉` (`q = |F|`).  Its docstring and
`PrizeConditionalPinCapstone.lean`'s honest correction both state -- in PROSE -- that at the prize
budget `q·ε* ≈ |G|` this conditional is VACUOUS: it forces `q·B ≤ 0`, i.e. `B = 0`, so no nonzero
char-sum / power-saving bound `B` (e.g. di Benedetto `B ≤ n^{1−31/2880}`) can satisfy it.  This was
never stated as a THEOREM.

This file discharges that prose obligation: the vacuity is a clean arithmetic consequence of the
ceiling budget, made into named, axiom-clean theorems.

## What is proved here (axiom-clean, no `sorry`)

* **`charSumBudget_ge_card`** -- `|G| ≤ charSumIncidenceBudget G B` for `B ≥ 0` (the budget never
  beats `|G|`; the naive count carries the full domain term `|G|`).
* **`charSumBudget_forces_B_zero`** -- the VACUITY core: if the ceiling budget meets the **prize
  budget** `charSumIncidenceBudget G B ≤ |G|` (`= ⌊q·ε*⌋` with `q·ε* = |G|`), and `q ≥ 1`,
  `B ≥ 0`, then `B = 0`.  `⌈|G|+q·B⌉ ≤ |G|` forces `q·B ≤ 0`, hence `B = 0`.
* **`charSumBudget_prize_excludes_positive`** -- contrapositive: any STRICTLY positive char-sum
  bound `B > 0` FAILS the prize incidence budget (`|G| < charSumIncidenceBudget G B`), so it cannot
  discharge the conditional pin via `le_mcaDeltaStar_of_charSumBound` at the prize budget.
* **`charSum_route_vacuous_at_prize`** -- the assembled statement: the trivial char-sum witness
  `B = |G|` (from `charSumBound_satisfiable_trivial`) is consistent but, for `|G| ≥ 1`, STRICTLY
  positive, hence excluded by the prize budget -- the only nonempty char-sum premise the route
  admits is the all-zero `B = 0`, which is FALSE (`‖η_b‖ = 0` for all `b ≠ 0` would make `μ_n` a
  perfect difference set, contra `b = 0` giving `‖η_0‖ = |G|`).  So the char-sum -> incidence route
  is VACUOUS at the prize budget: no `B` that the char-sum premise can actually certify also clears
  the prize budget.

## Honest scope (rule 3, rule 6)

This does NOT prove or refute CORE; it is the precise REACH delimiter of the *char-sum -> incidence*
discharge route, turning the in-tree PROSE correction ("`M` is necessary but insufficient; the naive
`|G|+q·B` budget is vacuous at `q·ε* ≈ n`") into a theorem.  It localizes WHY the BGK/Paley sup-norm
bound `M(n) ≤ C√(n·log m)` cannot, through this route, close the floor `hfloor` of
`PrizeConditionalPinCapstone`: the route's budget overshoots by the index factor.  The genuinely
finer realized-incidence object (`epsMCA` at the edge) is UNTOUCHED and remains the open prize core.
NON-MOMENT structural cardinality delimiter, EXTEND-proven on the proven in-tree budget bridge, NOT
a re-mapped dead face.  NO moment/census/geometric-minor re-derivation; NO capacity / beyond-Johnson
/ growth-law claim; cliff-at-n/2 untouched.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED / OPEN.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.CharSumBudgetVacuity

open ArkLib.ProximityGap.CharSumDeltaStarBridge

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The budget never beats `|G|`.**  For `B ≥ 0` the naive ceiling budget
`⌈|G| + q·B⌉` is at least the full domain size `|G|`. -/
theorem charSumBudget_ge_card (G : Finset F) {B : ℝ} (hB0 : 0 ≤ B) :
    G.card ≤ charSumIncidenceBudget (F := F) G B := by
  unfold charSumIncidenceBudget
  have hge : (G.card : ℝ) ≤ (G.card : ℝ) + (Fintype.card F : ℝ) * B := by
    have : (0 : ℝ) ≤ (Fintype.card F : ℝ) * B := by positivity
    linarith
  calc G.card = ⌈(G.card : ℝ)⌉₊ := (Nat.ceil_natCast _).symm
    _ ≤ ⌈(G.card : ℝ) + (Fintype.card F : ℝ) * B⌉₊ := Nat.ceil_le_ceil hge

/-- **VACUITY core.**  If the ceiling budget meets the prize budget `|G|` (`= ⌊q·ε*⌋` with the
prize relation `q·ε* = |G|`), with `q = |F| ≥ 1` and `B ≥ 0`, then `B = 0`.  The naive count carries
the whole `|G|` term, so `⌈|G| + q·B⌉ ≤ |G|` forces `q·B ≤ 0`, hence `B = 0`. -/
theorem charSumBudget_forces_B_zero (G : Finset F) {B : ℝ} (hB0 : 0 ≤ B)
    (hq : 1 ≤ Fintype.card F)
    (hbudget : charSumIncidenceBudget (F := F) G B ≤ G.card) :
    B = 0 := by
  -- `|G| + q·B ≤ ⌈|G| + q·B⌉ = charSumIncidenceBudget ≤ |G|`, so `q·B ≤ 0`.
  have hceil : ((charSumIncidenceBudget (F := F) G B : ℕ) : ℝ)
      ≥ (G.card : ℝ) + (Fintype.card F : ℝ) * B := by
    unfold charSumIncidenceBudget
    exact Nat.le_ceil _
  have hle : ((charSumIncidenceBudget (F := F) G B : ℕ) : ℝ) ≤ (G.card : ℝ) := by
    exact_mod_cast hbudget
  have hqB : (Fintype.card F : ℝ) * B ≤ 0 := by linarith
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hq)
  have hBle : B ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hqpos
  linarith

/-- **Prize budget excludes any positive bound.**  Contrapositive of `charSumBudget_forces_B_zero`:
a STRICTLY positive char-sum bound `B > 0` overshoots the prize incidence budget
(`|G| < charSumIncidenceBudget G B`), so it cannot discharge the conditional pin via
`le_mcaDeltaStar_of_charSumBound` at the prize budget `q·ε* = |G|`. -/
theorem charSumBudget_prize_excludes_positive (G : Finset F) {B : ℝ} (hB : 0 < B)
    (hq : 1 ≤ Fintype.card F) :
    G.card < charSumIncidenceBudget (F := F) G B := by
  rcases lt_or_ge (G.card : ℕ) (charSumIncidenceBudget (F := F) G B) with h | h
  · exact h
  · exact absurd (charSumBudget_forces_B_zero G hB.le hq h) (ne_of_gt hB)

/-- **The char-sum -> incidence route is VACUOUS at the prize budget.**  The trivial char-sum
witness `B = |G|` (`charSumBound_satisfiable_trivial`) is consistent, but for a nonempty domain
(`|G| ≥ 1`) it is STRICTLY positive, hence excluded by the prize incidence budget
(`charSumBudget_prize_excludes_positive`): `|G| < charSumIncidenceBudget G |G|`.  Thus the trivial
witness, the only unconditionally-available char-sum bound, does NOT clear the prize budget -- the
route cannot certify the floor at `q·ε* = |G|`.  (Any genuine power-saving `B = n^{1−c} > 0` is
excluded identically.) -/
theorem charSum_route_vacuous_at_prize {ψ : AddChar F ℂ} (G : Finset F)
    (hG : 1 ≤ G.card) (hq : 1 ≤ Fintype.card F) :
    G.card < charSumIncidenceBudget (F := F) G (G.card : ℝ) :=
  charSumBudget_prize_excludes_positive G (by exact_mod_cast hG) hq

end ArkLib.ProximityGap.CharSumBudgetVacuity

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.CharSumBudgetVacuity.charSumBudget_ge_card
#print axioms ArkLib.ProximityGap.CharSumBudgetVacuity.charSumBudget_forces_B_zero
#print axioms ArkLib.ProximityGap.CharSumBudgetVacuity.charSumBudget_prize_excludes_positive
#print axioms ArkLib.ProximityGap.CharSumBudgetVacuity.charSum_route_vacuous_at_prize
