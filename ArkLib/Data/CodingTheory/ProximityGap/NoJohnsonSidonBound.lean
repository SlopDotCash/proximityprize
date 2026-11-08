/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WorstPeriodSidonBound
import Mathlib.Tactic

/-!
# No Johnson-scale period in the Sidon regime (#389) — a correct, applicable sub-`√q` bound

The explicit no-Johnson threshold from the `r = 2` (4th-moment) Sidon bound. Unlike the general-`r`
full-Sidon lemmas (whose hypothesis `μ_n` fails), this uses the weaker hypothesis
`repCount G t ≤ 2` for `t ≠ 0` (Sidon *mod negation*). From `worst_period_sidon_le`
(`‖η_b‖⁴ ≤ 3·q·|G|²`):

> `worst_period_normsq_lt_card` :  if `repCount G t ≤ 2` for all `t ≠ 0` and `3|G|² < q`, then
> `‖η_b‖² < q` for every `b`.

So for a Sidon-mod-negation `G` with `|G| < √(q/3)`, **no** Gaussian period reaches the Johnson
scale `‖η_b‖² ≥ q`. The Sidon hypothesis is an explicit assumption and is **not** implied by the
size condition `3|G|² < q`.

**When does `μ_n` satisfy the hypothesis?** The in-tree producers establish it only in a much
smaller-`n` (exponentially large `q`) regime than `3n² < q`:
`smallSubgroup_sidonModNeg` (`SmallSubgroupSidonModNeg.lean`: `μ_n ⊆ F_p` is `SidonModNeg` when
`p > 2`, a primitive `n`-th root exists, and `4^{φ(n)} < p`) and `mu_n_isSidonModNeg`
(`SidonModNegEnergyEquality.lean`: `n = 2^m`, `m ≥ 1`, `2^n < p`). `SidonModNeg` gives the
`hrep` form used here via `WF2SidonRepTwo.repCount_le_two_of_sidonModNeg`
(`SmallSubgroupGVRepTwo.lean`). Outside that regime `μ_n` can fail the hypothesis even when
`3n² < q`: for `n = 32`, `q = 3137` (prime, `3·32² = 3072 < 3137`), the ordered pairs
`(1,56), (56,1), (1524,1670), (1670,1524)` of 32nd roots of unity all sum to `57`, so
`repCount μ_32 57 ≥ 4` (audit 2026-10-28, PG-023; a source-level computation, not a Lean
theorem). See also the kernel-checked `not_sidonModNeg_H16` (`μ_16 ⊆ F_257`,
`SidonModNegValidationFermat257.lean`). Empirical "near-Sidon" behaviour of `μ_n` at
moderate `q` is not exact `repCount ≤ 2` and does not discharge `hrep`. The full square-root
cancellation `√(n log f)` remains open.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.AdditiveEnergyRepBound
open ArkLib.ProximityGap.WorstPeriodSidon

namespace ArkLib.ProximityGap.WorstPeriodSidon

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **No Johnson-scale period in the Sidon regime.** If `G` is Sidon-mod-negation (`repCount G t ≤ 2`
for `t ≠ 0`) and `3|G|² < q`, then every Gaussian period satisfies `‖η_b‖² < q` — no period reaches the
Johnson scale. Applies to `μ_n` only where `repCount ≤ 2` has actually been established for it
(e.g. via `smallSubgroup_sidonModNeg` when `4^{φ(n)} < p`); `n < √(q/3)` alone does not supply
`hrep` (it fails for `n = 32`, `q = 3137`). -/
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
