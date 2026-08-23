/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.I031SubGaussianMaxBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# I031: landing the union bound at the PRIZE-TARGET log scale `log(q/n)` (#444)

The I031 dilation-quotient programme proved (axiom-clean, conditional on the named-open
per-period sub-Gaussian tail) the union bound

  `M(μ_n) = max_{b≠0} ‖η_b‖ ≤ √(2·C₀·n·log m)`,   `m = [F^*:μ_n] = (q−1)/n`

(`I031SubGaussianMaxBridge.i031_norm_eta_le_of_subGaussian`, with the orbit count `m = (q−1)/n`
pinned by `I031SupTransversalCollapse.transversal_card`). The prize TARGET, however, is stated
with `log(q/n)`, not `log m = log((q−1)/n)`. The open-directions census (§1.6) flagged the
**exact gap this file closes** as the next step: *"verify whether `log(p/n)` vs `log p` actually
changes the achievable constant."*

This file supplies the missing PURE-ALGEBRA layer connecting the orbit-count scale `(q−1)/n` to
the prize-target scale `q/n`, and re-expresses the conditional I031 bound directly in the
prize-target form. Two facts do all the work:

1. `log((q−1)/n) ≤ log(q/n)` -- so the proven bound at scale `m = (q−1)/n` is *a fortiori* a bound
   at the (larger) prize-target scale `log(q/n)`. The I031 union bound lands **at the prize
   target**, NOT merely at `log q`.
2. `log q − log(q/n) = log n` -- the dilation-quotient collapse removes **exactly** `log n` of
   metric entropy (the `√n`-scale the census names). This is the quantitative content of the
   "`log p → log(p/n)`" collapse: the gap between the trivial `√(n log q)` and the prize-target
   `√(n log(q/n))` is precisely the `log n` the orbit quotient discharges.

## What this delivers (axiom-clean)

- `log_div_pred_le_log_div` -- `log((q−1)/n) ≤ log(q/n)` for `0 < n`, `1 < q` (proper subgroup,
  `q ≥ 2`). So a bound at the orbit-count scale `(q−1)/n` lifts to the prize-target scale `q/n`.
- `log_sub_log_div_eq_log` -- `log q − log(q/n) = log n` for `0 < q`, `0 < n` (the removed entropy).
- `i031_norm_eta_le_logTarget` (HEADLINE) -- the I031 union bound re-stated at the prize-target
  scale: conditional on the SAME named-open sub-Gaussian tail (consumed via the proven bridge with
  `m = (q−1)/n`), `‖η_b‖ ≤ √(2·C₀·n·log(q/n))` for every `b`. The bound that was at scale
  `log((q−1)/n)` is lifted to the prize-target `log(q/n)` by monotonicity of `√` and `log`.
- `i031_logTarget_le_trivial` (rule-4 quantitative cartography) -- `√(2·C₀·n·log(q/n)) ≤
  √(2·C₀·n·log q)`: the prize-target bound sits BELOW the trivial `log q` bound, with the gap
  governed by the removed `log n` (`log_sub_log_div_eq_log`). Non-vacuous improvement, not a
  relabelling.
- `i031_M_le_logTarget` (M-LEVEL CAPSTONE) -- lifts the per-`b` bound to the literal prize object
  `M(μ_n) = (nonzeroFreqs F).sup' _ (‖η_·‖)` via `Finset.sup'_le`: `M(μ_n) ≤ √(2·(C₀·n)·log(q/n))`,
  conditional on the SAME open tail Prop. The full I031 deliverable at the M-level + prize-target.

## Honest scope

This is PURE real-analytic algebra (monotonicity of `log`/`√`, `log_div`) composed onto the
already-PROVEN conditional bridge. It does NOT touch the open input: the per-period sub-Gaussian
tail `SubGaussianTailBound (periodMagnitudes ψ G) (C₀·n) ((q−1)/n)` remains the SINGLE recognized-
open analytic Prop (the BGK/Lamzouri short-character-sum wall). **NO closure of CORE is claimed.**
The value here is frontier-movement: the census's named open verification (does the dilation
quotient land at `log(q/n)`?) is now a THEOREM -- yes, exactly, and the removed entropy is `log n`.
NON-MOMENT (pure DFT-orbit metric-entropy bookkeeping, not an additive-energy route).
ASYMPTOTIC-GUARD-COMPLIANT (a conditional union-bound at the Burgess/prize scale; no
capacity/beyond-Johnson/cliff-at-n/2 claim -- the residual is the tail Prop = the wall).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset AddChar

namespace ArkLib.ProximityGap.I031LogTargetForm

open ArkLib.ProximityGap.I031SubGaussianMaxBridge
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## 1. The pure-algebra log-scale facts -/

/-- **The orbit-count scale is below the prize-target scale.** For `0 < n` and `1 < q` (the proper
subgroup case `q ≥ 2`, so `(q−1)/n > 0`), `log((q−1)/n) ≤ log(q/n)`. Hence a bound proven at the
orbit-count scale `m = (q−1)/n` is a fortiori a bound at the prize-target scale `q/n`. -/
theorem log_div_pred_le_log_div {q n : ℝ} (hn : 0 < n) (hq : 1 < q) :
    Real.log ((q - 1) / n) ≤ Real.log (q / n) := by
  have hpos : 0 < (q - 1) / n := by
    apply div_pos _ hn; linarith
  have hle : (q - 1) / n ≤ q / n := by
    gcongr
    linarith
  exact Real.log_le_log hpos hle

/-- **The removed metric entropy is exactly `log n`.** For `0 < q`, `0 < n`,
`log q − log(q/n) = log n`. This is the quantitative content of the I031 `log p → log(p/n)`
collapse: the dilation quotient discharges precisely `log n` of entropy (the `√n` scale). -/
theorem log_sub_log_div_eq_log {q n : ℝ} (hq : 0 < q) (hn : 0 < n) :
    Real.log q - Real.log (q / n) = Real.log n := by
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hn)]
  ring

/-! ## 2. The I031 union bound at the prize-target scale (conditional, via the proven bridge) -/

/-- **The I031 union bound, re-stated at the prize-target scale `log(q/n)`.** With proxy variance
`C₀·n` (`0 < C₀·n`), prize regime `1 < q` and `0 < n`, and orbit count `m = (q−1)/n`, if the
period magnitudes satisfy the named-open sub-Gaussian tail bound (the SAME hypothesis the proven
bridge consumes), then **every** period magnitude is bounded at the prize-target scale:

> `‖η_b‖ ≤ √(2·(C₀·n)·log(q/n))`.

*Proof.* The proven bridge `i031_norm_eta_le_of_subGaussian` gives
`‖η_b‖ ≤ √(2·(C₀·n)·log((q−1)/n))` (orbit-count scale `m = (q−1)/n`). Then
`log((q−1)/n) ≤ log(q/n)` (`log_div_pred_le_log_div`) lifts the radicand, and `√` is monotone.

This is the census §1.6 verification, now a theorem: the dilation-quotient collapse lands the
union bound **at the prize target `log(q/n)`**. The residual is the tail Prop = the BGK wall. -/
theorem i031_norm_eta_le_logTarget {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) {C₀ n q : ℝ}
    (hC : 0 < C₀ * n) (hn : 0 < n) (hq : 1 < q) (hindex : n ≤ q - 1)
    (h : SubGaussianTailBound (periodMagnitudes ψ G) (C₀ * n) ((q - 1) / n)) (b : F) :
    ‖eta ψ G b‖ ≤ Real.sqrt (2 * (C₀ * n) * Real.log (q / n)) := by
  -- the orbit count m = (q−1)/n ≥ 1 since the subgroup μ_n has index ≥ 1 (n ≤ q−1, as n ∣ q−1)
  have hm : (1 : ℝ) ≤ (q - 1) / n := (one_le_div hn).mpr hindex
  have hbridge := i031_norm_eta_le_of_subGaussian ψ G hC hm h b
  apply le_trans hbridge
  apply Real.sqrt_le_sqrt
  have hlog := log_div_pred_le_log_div (q := q) (n := n) hn hq
  nlinarith [hC, hlog]

/-- **The prize-target bound sits below the trivial `log q` bound** (rule-4 quantitative
cartography). For `0 ≤ C₀·n`, `0 < q`, `0 < n` with `1 ≤ n` (so `log n ≥ 0`):
`√(2·(C₀·n)·log(q/n)) ≤ √(2·(C₀·n)·log q)`. The gap in the radicands is exactly
`2·(C₀·n)·log n` by `log_sub_log_div_eq_log` (the removed entropy). So the I031 prize-target
bound is a GENUINE improvement over the trivial `log q` union bound (not a relabelling): the
dilation quotient discharges the `√n`-scale `log n`. -/
theorem i031_logTarget_le_trivial {C₀ n q : ℝ}
    (hC : 0 ≤ C₀ * n) (hq : 0 < q) (hn : 0 < n) (hn1 : 1 ≤ n) :
    Real.sqrt (2 * (C₀ * n) * Real.log (q / n))
      ≤ Real.sqrt (2 * (C₀ * n) * Real.log q) := by
  apply Real.sqrt_le_sqrt
  have hgap : Real.log q - Real.log (q / n) = Real.log n :=
    log_sub_log_div_eq_log hq hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  nlinarith [hC, hgap, hlogn]

/-! ## 3. The M-level capstone: the actual `M(μ_n) = sup' ‖η_·‖` at the prize target -/

open ArkLib.ProximityGap.I031DilationOrbitReduction

/-- **The I031 union bound on the literal `M(μ_n)`, at the prize-target scale.** The prize object
is `M(μ_n) = max_{b≠0} ‖η_b‖ = (nonzeroFreqs F).sup' _ (‖η_·‖)`. The per-`b` bound
`i031_norm_eta_le_logTarget` holds for EVERY `b`, so `Finset.sup'_le` lifts it to the sup itself:

> `M(μ_n) = (nonzeroFreqs F).sup' hne (‖η_·‖) ≤ √(2·(C₀·n)·log(q/n))`,

conditional on the SAME named-open per-period sub-Gaussian tail (the BGK/Lamzouri wall). This is
the full I031 deliverable at the M-level and the prize-target scale: the dilation-quotient collapse
lands the maximum period magnitude at `√(n·log(q/n))` (up to the conditional constant), NOT the
trivial `√(n·log q)`. The residual is the tail Prop = the wall; NO CORE closure is claimed. -/
theorem i031_M_le_logTarget {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) {C₀ n q : ℝ}
    (hC : 0 < C₀ * n) (hn : 0 < n) (hq : 1 < q) (hindex : n ≤ q - 1)
    (h : SubGaussianTailBound (periodMagnitudes ψ G) (C₀ * n) ((q - 1) / n))
    (hne : (nonzeroFreqs F).Nonempty) :
    (nonzeroFreqs F).sup' hne (fun b => ‖eta ψ G b‖)
      ≤ Real.sqrt (2 * (C₀ * n) * Real.log (q / n)) := by
  apply Finset.sup'_le
  intro b _
  exact i031_norm_eta_le_logTarget ψ G hC hn hq hindex h b

end ArkLib.ProximityGap.I031LogTargetForm

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.I031LogTargetForm.log_div_pred_le_log_div
#print axioms ArkLib.ProximityGap.I031LogTargetForm.log_sub_log_div_eq_log
#print axioms ArkLib.ProximityGap.I031LogTargetForm.i031_norm_eta_le_logTarget
#print axioms ArkLib.ProximityGap.I031LogTargetForm.i031_logTarget_le_trivial
#print axioms ArkLib.ProximityGap.I031LogTargetForm.i031_M_le_logTarget
