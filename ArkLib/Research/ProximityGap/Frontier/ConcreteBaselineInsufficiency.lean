/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The √q-completion baseline does NOT close the prize: the normalized gap is real (#444)

The Lane-2 chain proves, unconditionally over the real periods, the normalized SOTA corridor
`Sh(M(μ_n)) ≤ √(q/(n·L))` (`ConcreteShawCompletionCorridor`). The prize asks for `Sh(M(μ_n)) ≤ C`
(`O(1)`). This file records the honest arithmetic fact that the baseline corridor is STRICTLY
INSUFFICIENT in the prize regime: once the thinness ratio `q/(n·L)` exceeds `C²`, the proven baseline
bound `√(q/(n·L))` is itself `> C`, so it cannot certify the prize.

> `sqrt_ratio_gt_of_lt`         : `C² < q/(n·L) → C < √(q/(n·L))`  (the baseline exceeds the target),
> `baseline_insufficient`       : in the thin regime `C² · (n·L) < q`, the proven ceiling
>                                 `√(q/(n·L))` does NOT imply `Sh ≤ C` — the gap is real.
> `trivial_ceiling_insufficient`: in the even weaker triangle regime `C² · L < n`, the trivial
>                                 normalized ceiling `√(n/L)` also exceeds `C`.

In the prize regime `n = 2^a`, `q = n^β` (`β ≈ 4-5`), `L = log(p/n) = Θ(log q)`, the ratio is
`q/(n·L) = n^{β−1}/Θ(log q) → ∞`, so for every fixed `C` the hypothesis `C²·(n·L) < q` holds for all
large `n`: the √q-completion baseline is unboundedly far above the prize target. The prize is exactly
the (open) statement that the TRUE Shaw value stays `O(1)` despite the baseline diverging.

## Honesty (this is a NEGATIVE/limiting fact, not progress on CORE)

This proves only that the unconditional baseline corridor cannot, by itself, give the prize — it
quantifies the open gap, it does not narrow it. No cancellation, anti-concentration, moment, or
completion-saving content. CORE `Sh(M(μ_n)) = O(1)` stays OPEN; this is the precise statement that
the proven upper rung leaves it open.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ProximityGap.Frontier.ConcreteBaselineInsufficiency

/-- **The baseline exceeds the prize target when the thinness ratio is large.** If `0 ≤ C` and
`C² < R` then `C < √R`. Applied with `R = q/(n·L)`: once `q/(n·L) > C²`, the proven SOTA baseline
`√(q/(n·L))` is itself `> C`, so it cannot certify `Sh ≤ C`. -/
theorem sqrt_ratio_gt_of_lt {C R : ℝ} (hC : 0 ≤ C) (h : C ^ 2 < R) :
    C < Real.sqrt R := by
  have hCsq : Real.sqrt (C ^ 2) = C := by
    rw [Real.sqrt_sq hC]
  calc C = Real.sqrt (C ^ 2) := hCsq.symm
    _ < Real.sqrt R := Real.sqrt_lt_sqrt (sq_nonneg C) h

/-- **Baseline insufficiency in the thin prize regime.** With positive subgroup size `n` and positive
thinness `L`, if `C² · (n·L) < q` (the thin regime, where `q/(n·L) > C²`), then the proven SOTA
baseline `√(q/(n·L))` strictly exceeds `C`. Hence the unconditional ceiling `Sh ≤ √(q/(n·L))` does
NOT yield the prize `Sh ≤ C` — the normalized gap is real and the prize remains a genuine saving
that the baseline does not supply. -/
theorem baseline_insufficient {C n L q : ℝ} (hC : 0 ≤ C) (hn : 0 < n) (hL : 0 < L)
    (hthin : C ^ 2 * (n * L) < q) :
    C < Real.sqrt (q / (n * L)) := by
  have hnL : 0 < n * L := mul_pos hn hL
  have hratio : C ^ 2 < q / (n * L) := by
    rw [lt_div_iff₀ hnL]; exact hthin
  exact sqrt_ratio_gt_of_lt hC hratio

/-- **The triangle/trivial ceiling is also insufficient in the prize normalization.** The normalized
form of `M ≤ n` is `√(n/L)`.  If `C² · L < n` (true for every fixed `C` at large `n` when
`L = Θ(log n)`), then this trivial normalized ceiling strictly exceeds the target `C`; therefore the
plain triangle bound carries no `O(1)` Shaw-value certificate. -/
theorem trivial_ceiling_insufficient {C n L : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hthin : C ^ 2 * L < n) :
    C < Real.sqrt (n / L) := by
  have hratio : C ^ 2 < n / L := by
    rw [lt_div_iff₀ hL]
    exact hthin
  exact sqrt_ratio_gt_of_lt hC hratio

/-- Contradiction form: in the thin regime, the completion baseline cannot simultaneously be below
`C`.  This is the exact no-go consumer for attempts to close the prize using only the proven
`√(q/(n·L))` normalized corridor. -/
theorem not_completion_baseline_certifies_in_thin_regime {C n L q : ℝ} (hC : 0 ≤ C)
    (hn : 0 < n) (hL : 0 < L) (hthin : C ^ 2 * (n * L) < q) :
    ¬ Real.sqrt (q / (n * L)) ≤ C := by
  intro hcert
  have hgap : C < Real.sqrt (q / (n * L)) := baseline_insufficient hC hn hL hthin
  linarith

/-- Contradiction form for the triangle/trivial ceiling: in the prize normalization regime where
`C² · L < n`, the normalized triangle ceiling `√(n/L)` cannot itself be a certificate below `C`.
This pins the no-go consumer for attempts to close the Shaw-value target using only `M ≤ n`. -/
theorem not_trivial_ceiling_certifies_in_thin_regime {C n L : ℝ} (hC : 0 ≤ C)
    (hL : 0 < L) (hthin : C ^ 2 * L < n) :
    ¬ Real.sqrt (n / L) ≤ C := by
  intro hcert
  have hgap : C < Real.sqrt (n / L) := trivial_ceiling_insufficient hC hL hthin
  linarith

/-- Even taking the better of the two unconditional classical ceilings does not certify a bounded
Shaw value in the simultaneous thin regime.  If both the completion ceiling and triangle ceiling
exceed `C`, then their pointwise minimum also exceeds `C`. -/
theorem classical_min_baseline_insufficient {C n L q : ℝ} (hC : 0 ≤ C) (hn : 0 < n)
    (hL : 0 < L) (hcompletion : C ^ 2 * (n * L) < q) (htriangle : C ^ 2 * L < n) :
    C < min (Real.sqrt (q / (n * L))) (Real.sqrt (n / L)) := by
  have hcomp : C < Real.sqrt (q / (n * L)) :=
    baseline_insufficient hC hn hL hcompletion
  have htri : C < Real.sqrt (n / L) := trivial_ceiling_insufficient hC hL htriangle
  exact lt_min hcomp htri

/-- Contradiction form for the combined classical corridor: in the simultaneous thin regime, neither
`√q` completion nor the trivial triangle ceiling, nor the better of the two, supplies a certificate
`≤ C`.  Any bounded Shaw-value proof must use new cancellation beyond these classical rungs. -/
theorem not_classical_min_baseline_certifies_in_thin_regime {C n L q : ℝ} (hC : 0 ≤ C)
    (hn : 0 < n) (hL : 0 < L) (hcompletion : C ^ 2 * (n * L) < q)
    (htriangle : C ^ 2 * L < n) :
    ¬ min (Real.sqrt (q / (n * L))) (Real.sqrt (n / L)) ≤ C := by
  intro hcert
  have hgap : C < min (Real.sqrt (q / (n * L))) (Real.sqrt (n / L)) :=
    classical_min_baseline_insufficient hC hn hL hcompletion htriangle
  linarith

end ProximityGap.Frontier.ConcreteBaselineInsufficiency

#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.sqrt_ratio_gt_of_lt
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.baseline_insufficient
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.trivial_ceiling_insufficient
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.not_completion_baseline_certifies_in_thin_regime
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.not_trivial_ceiling_certifies_in_thin_regime
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.classical_min_baseline_insufficient
#print axioms ProximityGap.Frontier.ConcreteBaselineInsufficiency.not_classical_min_baseline_certifies_in_thin_regime
