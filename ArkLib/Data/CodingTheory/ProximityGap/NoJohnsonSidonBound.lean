/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodSidonBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.longLine false

/-!
# No Johnson-scale period in the Sidon regime (#389) — a correct, applicable sub-`√q` bound

The explicit no-Johnson threshold from the `r = 2` (4th-moment) Sidon bound. Unlike the general-`r`
full-Sidon lemmas (whose hypothesis `μ_n` fails), this uses `repCount ≤ 2` (Sidon *mod negation*),
which `μ_n` DOES satisfy. From `worst_period_sidon_le` (`‖η_b‖⁴ ≤ 3·q·|G|²`):

> `worst_period_normsq_lt_card` :  if `3|G|² < q` then `‖η_b‖² < q` for every `b`.

So for `|G| < √(q/3)` (and in particular `|G| < √q`), **no** Gaussian period reaches the Johnson scale
`‖η_b‖² ≥ q` — a genuine sub-`√q` worst-period bound that applies to `μ_n`. (This is the correct,
`μ_n`-applicable counterpart of the no-Johnson threshold; the full square-root cancellation `√(n log f)`
remains the open part.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.WorstPeriodSidon

namespace ArkLib.ProximityGap.WorstPeriodSidon

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **No Johnson-scale period in the Sidon regime.** If `G` is Sidon-mod-negation (`repCount G t ≤ 2`
for `t ≠ 0`) and `3|G|² < q`, then every Gaussian period satisfies `‖η_b‖² < q` — no period reaches the
Johnson scale. Applies to `μ_n` (which satisfies `repCount ≤ 2`) whenever `n < √(q/3)`. -/
theorem worst_period_normsq_lt_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hrep : ∀ t : F, t ≠ 0 → repCount G t ≤ 2)
    (hsmall : 3 * (G.card : ℝ) ^ 2 < (Fintype.card F : ℝ)) (b : F) :
    ‖eta ψ G b‖ ^ 2 < (Fintype.card F : ℝ) := by
  have h4 := worst_period_sidon_le hψ G hrep b
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) := lt_of_le_of_lt (by positivity) hsmall
  -- ‖η_b‖⁴ ≤ 3·q·|G|² < q·q = q²
  have hsq : (‖eta ψ G b‖ ^ 2) ^ 2 < (Fintype.card F : ℝ) ^ 2 := by
    have e : (‖eta ψ G b‖ ^ 2) ^ 2 = ‖eta ψ G b‖ ^ 4 := by ring
    rw [e]
    nlinarith [h4, hsmall, hq0]
  have hynn : (0 : ℝ) ≤ ‖eta ψ G b‖ ^ 2 := by positivity
  nlinarith [hsq, hq0, hynn, sq_nonneg (‖eta ψ G b‖ ^ 2 - (Fintype.card F : ℝ))]

end ArkLib.ProximityGap.WorstPeriodSidon

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WorstPeriodSidon.worst_period_normsq_lt_card
