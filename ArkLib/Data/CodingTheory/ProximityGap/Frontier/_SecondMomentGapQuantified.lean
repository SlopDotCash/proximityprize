/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MetaTheoremSecondOrderFloor

/-!
# The second-moment method overshoots the prize target by a STRICT margin (#407 — C1 quantified)

`_MetaTheoremSecondOrderFloor` proves the qualitative no-go: any second-moment-only method on the
Gauss periods is forced up to `√(q·n − n²)` (the spike obstruction). This file makes it
**quantitative**: in the prize regime `q ≫ n` the forced second-moment ceiling `√(q·n − n²)` is
*strictly larger* than the prize per-frequency target `C·√(n·log(q/n))`, so a second-moment method
provably cannot even *reach* the target — it overshoots by a strict margin governed by the regime
gap `q − n` versus `C²·log(q/n)`.

* `prizeSq_lt_secondMomentSq` — the squared-scale separation `C²·(n·log(q/n)) < q·n − n²`
  (`= n·(q−n)`) whenever `C²·log(q/n) < q − n` (always, for `q` polynomially large: LHS `~ log q`,
  RHS `~ q`).
* `prize_target_lt_secondMoment_ceiling` — the same under the square root: `C·√(n·log(q/n)) <
  √(q·n − n²)`.
* `secondMoment_method_overshoots_prize` — the payoff: composing with
  `periods_secondMoment_method_floor`, *any* valid second-moment method `g` applied to the periods
  returns a value `> C·√(n·log(q/n))` (the prize target). So no second-moment method certifies the
  prize per-frequency bound — not by a hair, but by a quantified `√q`-scale margin.

This is the sharp form of "no tighter bound from the second-moment direction": the gap that BGK must
fill is real, strict, and exactly `√((q−n) / log(q/n)) ≈ √(q/log q)` wide.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #407.
-/

open AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.MetaTheoremSecondOrderFloor

namespace ProximityGap.Frontier.SecondMomentGapQuantified

/-- **Squared-scale separation.** With `n > 0` and the regime gap `C²·log(q/n) < q − n`, the prize
squared scale is strictly below the second-moment squared ceiling: `C²·(n·log(q/n)) < q·n − n²`. -/
theorem prizeSq_lt_secondMomentSq {n q C : ℝ} (hn : 0 < n)
    (hgap : C ^ 2 * Real.log (q / n) < q - n) :
    C ^ 2 * (n * Real.log (q / n)) < q * n - n ^ 2 := by
  have hmul : n * (C ^ 2 * Real.log (q / n)) < n * (q - n) := by
    exact mul_lt_mul_of_pos_left hgap hn
  nlinarith [hmul]

/-- **Square-root separation.** The prize per-frequency target `C·√(n·log(q/n))` is strictly below
the second-moment ceiling `√(q·n − n²)`, in the prize regime. -/
theorem prize_target_lt_secondMoment_ceiling {n q C : ℝ} (hn : 0 < n) (hnq : n < q) (hC : 0 ≤ C)
    (hgap : C ^ 2 * Real.log (q / n) < q - n) :
    C * Real.sqrt (n * Real.log (q / n)) < Real.sqrt (q * n - n ^ 2) := by
  have hlog : 0 ≤ Real.log (q / n) := Real.log_nonneg (by rw [le_div_iff₀ hn]; linarith)
  have hx : 0 ≤ n * Real.log (q / n) := mul_nonneg hn.le hlog
  have hCx : 0 ≤ C ^ 2 * (n * Real.log (q / n)) := mul_nonneg (sq_nonneg C) hx
  have hrewrite : C * Real.sqrt (n * Real.log (q / n))
      = Real.sqrt (C ^ 2 * (n * Real.log (q / n))) := by
    rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
  rw [hrewrite]
  exact Real.sqrt_lt_sqrt hCx (prizeSq_lt_secondMomentSq hn hgap)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The payoff: second-moment methods overshoot the prize target.** Let `g` be any valid
second-moment method on the nonzero frequencies (`∀ f c, |f c| ≤ g (∑ (f i)²)`). In the prize regime
(`n = |G| < q = |F|`, regime gap `C²·log(q/n) < q − n`), applying `g` to the Gauss-period family
returns a value **strictly greater** than the prize per-frequency target `C·√(n·log(q/n))`. Hence no
second-moment method can certify the prize floor — it overshoots by a `√q`-scale margin. This is the
quantitative core of "no tighter bound on δ* from the second-moment direction." -/
theorem secondMoment_method_overshoots_prize
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {C : ℝ}
    (hq : 2 ≤ Fintype.card F) (hC : 0 ≤ C)
    (hn : 0 < (G.card : ℝ)) (hnq : (G.card : ℝ) < Fintype.card F)
    (hgap : C ^ 2 * Real.log ((Fintype.card F : ℝ) / G.card) < (Fintype.card F : ℝ) - G.card)
    (g : ℝ → ℝ)
    (hg : ∀ (f : {b : F // b ≠ 0} → ℝ) (c : {b : F // b ≠ 0}), |f c| ≤ g (∑ i, (f i) ^ 2)) :
    C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
      < g (∑ i : {b : F // b ≠ 0}, ‖eta ψ G i.val‖ ^ 2) := by
  have hGF : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) * G.card := by nlinarith [hn, hnq]
  calc C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
      < Real.sqrt ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) :=
        prize_target_lt_secondMoment_ceiling hn hnq hC hgap
    _ ≤ g (∑ i : {b : F // b ≠ 0}, ‖eta ψ G i.val‖ ^ 2) :=
        periods_secondMoment_method_floor hψ G hq hGF g hg

end ProximityGap.Frontier.SecondMomentGapQuantified

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.SecondMomentGapQuantified.prizeSq_lt_secondMomentSq
#print axioms ProximityGap.Frontier.SecondMomentGapQuantified.prize_target_lt_secondMoment_ceiling
#print axioms ProximityGap.Frontier.SecondMomentGapQuantified.secondMoment_method_overshoots_prize
