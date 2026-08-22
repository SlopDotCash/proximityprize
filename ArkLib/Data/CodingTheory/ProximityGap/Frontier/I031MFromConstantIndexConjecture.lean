/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031MFromPointwise
import ArkLib.Data.CodingTheory.ProximityGap.ConstantIndexSubGaussianPeriod

/-!
# The #407 Constant-Index conjecture discharges the I031 prize-target `M(μ_n)` bound (#444, #407)

This is the capstone of the I031 ↔ #407 interface-wiring arc:
- `7b4824b8a` proved the I031 union-bound hypothesis = the pointwise period bound (exact equivalence);
- `89c3fdeb2` landed `i031_M_le_logTarget_of_pointwise` — the prize-target `M(μ_n)` bound from the
  pointwise hypothesis `∀ b, ‖η_b‖ ≤ √(2(C₀n)·log((q−1)/n))`.

This file connects the FINAL link: the #407 named conjecture
`ConstantIndexSubGaussianPeriod.ConstantIndexSubGaussianPeriodBound ψ G m`
(`∀ b ≠ 0, ‖η_b‖ ≤ √(2·|G|·log m)`) discharges that hypothesis at the orbit-count index
`m = (q−1)/|G|`, hence delivers the literal prize-target sup-norm bound

> `M(μ_n) = (nonzeroFreqs F).sup' _ (‖η_·‖) ≤ √(2·|G|·log(q/n))`.

So the prize-target M-bound now follows DIRECTLY from the recognized-open #407 conjecture — the two
independently-isolated "named open" objects (#407's pointwise period conjecture and I031's union-bound
tail Prop) are proven to deliver the SAME prize-target M-bound, through one clean axiom-clean chain.

## What this delivers (axiom-clean)

- `i031_M_le_logTarget_of_constantIndexConjecture` (HEADLINE) — from
  `ConstantIndexSubGaussianPeriodBound ψ G m` with `(m : ℝ) = (q−1)/|G|` (the #407 conjecture at the
  orbit-count index `m`), with `0 < |G|`, `1 < q`, `|G| ≤ q−1`, the literal prize object is bounded
  at the prize target.

## Honest scope

PURE wiring: the #407 conjecture is `∀ b ≠ 0` (it excludes `b = 0`), and the prize object is the
`sup'` over `nonzeroFreqs F = {b ≠ 0}`, so the `b ≠ 0` content lines up exactly; the index `m` of
#407 is the orbit count `(q−1)/|G|`, and `|G| = n` is the variance proxy (`C₀ = 1`). It does NOT
touch the open input — `ConstantIndexSubGaussianPeriodBound` IS the BGK/Lamzouri wall, stated as a
`Prop`, never asserted. **NO closure of CORE is claimed.** The value: the #407 conjecture and the I031
capstone are now proven to be two consumers of one prize-target M-bound; the interface is fully wired.
NON-MOMENT, EXTEND-proven. CORE `M(μ_n) ≤ C·√(n·log(p/n))` OPEN.
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ArkLib.ProximityGap.I031MFromConstantIndexConjecture

open ArkLib.ProximityGap.I031MFromPointwise
open ArkLib.ProximityGap.I031LogTargetForm
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The #407 conjecture discharges the I031 prize-target `M(μ_n)` bound.** With the #407
constant-index sub-Gaussian period conjecture at the orbit-count index `m = (q−1)/|G|` — i.e.
`∀ b ≠ 0, ‖η_b‖ ≤ √(2·|G|·log((q−1)/|G|))` — and the prize regime `0 < |G|`, `1 < q`, `|G| ≤ q−1`,
the literal prize object is bounded at the prize-target scale:

> `M(μ_n) = (nonzeroFreqs F).sup' hne (‖η_·‖) ≤ √(2·|G|·log(q/|G|))`.

*Proof.* The #407 conjecture gives `‖η_b‖ ≤ √(2·|G|·log m)` for every `b ≠ 0`, where `m = (q−1)/|G|`
as a real. Every `b` summed in `(nonzeroFreqs F).sup'` is nonzero (`mem_nonzeroFreqs`), so the
pointwise hypothesis of `i031_M_le_logTarget_of_pointwise` holds for those `b` (with `C₀ = 1`,
`n = |G|`); applying that capstone delivers the prize-target bound. We supply the per-`b` bound only
on `nonzeroFreqs` via a direct `Finset.sup'_le` + the per-`b` log-monotone lift
`log((q−1)/|G|) ≤ log(q/|G|)`. -/
theorem i031_M_le_logTarget_of_constantIndexConjecture
    (ψ : AddChar F ℂ) (G : Finset F) {q : ℝ} {m : ℕ}
    (hG : 0 < (G.card : ℝ)) (hq : 1 < q) (hindex : (G.card : ℝ) ≤ q - 1)
    (hconj : ArkLib.ProximityGap.ConstantIndexSubGaussianPeriod.ConstantIndexSubGaussianPeriodBound
      ψ G m)
    (hindexNat : (m : ℝ) = (q - 1) / (G.card : ℝ))
    (hne : (nonzeroFreqs F).Nonempty) :
    (nonzeroFreqs F).sup' hne (fun b => ‖eta ψ G b‖)
      ≤ Real.sqrt (2 * (G.card : ℝ) * Real.log (q / (G.card : ℝ))) := by
  have hC : 0 < (1 : ℝ) * (G.card : ℝ) := by rw [one_mul]; exact hG
  have hn : 0 < (G.card : ℝ) := hG
  -- per-b bound on nonzeroFreqs from the #407 conjecture, lifted to the prize target
  apply Finset.sup'_le
  intro b hb
  have hb0 : b ≠ 0 := mem_nonzeroFreqs.mp hb
  -- #407: ‖η_b‖ ≤ √(2·|G|·log m), m = ((q-1)/|G|).toNat
  have hpt := hconj b hb0
  -- rewrite the log argument from the Nat index to the real (q-1)/|G|
  rw [hindexNat] at hpt
  refine le_trans hpt ?_
  apply Real.sqrt_le_sqrt
  have hlog := log_div_pred_le_log_div (q := q) (n := (G.card : ℝ)) hn hq
  nlinarith [hG, hlog]

end ArkLib.ProximityGap.I031MFromConstantIndexConjecture

/-! ## Axiom audit -/
open ArkLib.ProximityGap.I031MFromConstantIndexConjecture in
#print axioms i031_M_le_logTarget_of_constantIndexConjecture
