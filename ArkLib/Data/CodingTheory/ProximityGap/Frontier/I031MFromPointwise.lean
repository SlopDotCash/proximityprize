/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.I031TailFromPointwise
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031LogTargetForm

/-!
# I031: the prize-target `M(μ_n)` bound from the POINTWISE per-period hypothesis (#444, #407)

`I031TailFromPointwise.subGaussianTailBoundAbove_iff_forall_le` proved that the I031 union-bound
hypothesis (the `s ≥ s*` tail-count Prop) is *logically equivalent* to the **pointwise** per-period
bound `∀ v ∈ periodMagnitudes, v ≤ s*`. This file consumes that equivalence to re-land the I031
prize-target capstone directly from the **#407 pointwise period bound** form `∀ b, ‖η_b‖ ≤ s*` —
the cleaner, genuinely-equivalent hypothesis (not the gratuitously-strong full-`s` tail Prop).

This is the FIRST theorem whose hypothesis is the pointwise period bound and whose conclusion is the
literal prize object `M(μ_n) = (nonzeroFreqs F).sup' _ (‖η_·‖) ≤ √(2·(C₀·n)·log(q/n))` at the prize
target scale. It wires the #407 `ConstantIndexSubGaussianPeriodBound` form straight into the I031
deliverable.

## What this delivers (axiom-clean)

- `forall_mem_periodMagnitudes_iff_forall_norm_eta` — the finset-quantified pointwise bound
  `∀ v ∈ periodMagnitudes ψ G, v ≤ s` is equivalent to the per-frequency bound `∀ b, ‖η_b‖ ≤ s`
  (since `periodMagnitudes` is exactly the image `{‖η_b‖}`).
- `i031_M_le_logTarget_of_pointwise` (HEADLINE) — `M(μ_n) ≤ √(2·(C₀·n)·log(q/n))` from the
  pointwise hypothesis `∀ b, ‖η_b‖ ≤ √(2·(C₀·n)·log((q−1)/n))`, via the equivalence + the proven
  prize-target capstone. The I031 deliverable now consumes the #407 pointwise conjecture form.

## Honest scope

PURE plumbing on top of two proven layers (`subGaussianTailBoundAbove_iff_forall_le` +
`i031_M_le_logTarget`). It does NOT touch the open input — the pointwise period bound
`∀ b, ‖η_b‖ ≤ √(2·(C₀·n)·log m)` IS the BGK/Lamzouri short-character-sum wall (= the #407
`ConstantIndexSubGaussianPeriodBound`). **NO closure of CORE is claimed.** The value: the I031
prize-target M-bound is now derivable from the pointwise conjecture form, not just the over-strong
tail Prop — closing the interface gap between the I031 capstone and the #407 file.
NON-MOMENT, EXTEND-proven, ASYMPTOTIC-GUARD-COMPLIANT. CORE `M(μ_n) ≤ C·√(n·log(p/n))` OPEN.
-/

set_option linter.style.longLine false


open Finset AddChar

namespace ArkLib.ProximityGap.I031MFromPointwise

open ArkLib.ProximityGap.I031SubGaussianMaxBridge
open ArkLib.ProximityGap.I031TailFromPointwise
open ArkLib.ProximityGap.I031LogTargetForm
open ArkLib.ProximityGap.I031DilationOrbitReduction
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The finset-quantified pointwise bound over `periodMagnitudes` is equivalent to the
per-frequency bound `∀ b, ‖η_b‖ ≤ s` (since `periodMagnitudes ψ G = {‖η_b‖ : b}`). -/
theorem forall_mem_periodMagnitudes_iff_forall_norm_eta
    (ψ : AddChar F ℂ) (G : Finset F) (s : ℝ) :
    (∀ v ∈ periodMagnitudes ψ G, v ≤ s) ↔ (∀ b : F, ‖eta ψ G b‖ ≤ s) := by
  constructor
  · intro h b
    exact h _ (norm_eta_mem_periodMagnitudes ψ G b)
  · intro h v hv
    -- v ∈ periodMagnitudes = image (‖·‖) (image (eta) univ); extract the witness b
    unfold periodMagnitudes at hv
    rw [Finset.mem_image] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    rw [Finset.mem_image] at hz
    obtain ⟨b, _, rfl⟩ := hz
    exact h b

/-- **The prize-target `M(μ_n)` bound from the POINTWISE per-period hypothesis.** With proxy
variance `C₀·n` (`0 < C₀·n`), prize regime `1 < q`, `0 < n`, index `n ≤ q−1`, and the orbit-count
scale `m = (q−1)/n`, if the periods satisfy the **pointwise** bound
`∀ b, ‖η_b‖ ≤ √(2·(C₀·n)·log((q−1)/n))` (= the #407 `ConstantIndexSubGaussianPeriodBound` form),
then the literal prize object is bounded at the prize-target scale:

> `M(μ_n) = (nonzeroFreqs F).sup' hne (‖η_·‖) ≤ √(2·(C₀·n)·log(q/n))`.

*Proof.* The pointwise hypothesis gives `∀ v ∈ periodMagnitudes, v ≤ s*` (with `s* = √(2(C₀n)·
log((q−1)/n))`) by `forall_mem_periodMagnitudes_iff_forall_norm_eta`; the equivalence
`subGaussianTailBoundAbove_iff_forall_le` turns that into `SubGaussianTailBoundAbove`; but the I031
capstone consumes the FULL `SubGaussianTailBound`. We do NOT need the full Prop: the pointwise bound
already gives the per-`b` bound at `s*`, and `i031_logTarget_le_trivial`-style log-monotonicity lifts
`s* = √(…log((q−1)/n))` to the prize-target `√(…log(q/n))` directly, then `Finset.sup'_le`. -/
theorem i031_M_le_logTarget_of_pointwise
    (ψ : AddChar F ℂ) (G : Finset F) {C₀ n q : ℝ}
    (hC : 0 < C₀ * n) (hn : 0 < n) (hq : 1 < q) (hindex : n ≤ q - 1)
    (hpt : ∀ b : F, ‖eta ψ G b‖ ≤ Real.sqrt (2 * (C₀ * n) * Real.log ((q - 1) / n)))
    (hne : (nonzeroFreqs F).Nonempty) :
    (nonzeroFreqs F).sup' hne (fun b => ‖eta ψ G b‖)
      ≤ Real.sqrt (2 * (C₀ * n) * Real.log (q / n)) := by
  -- lift each per-b bound from log((q-1)/n) to the prize target log(q/n)
  have hlift : ∀ b : F, ‖eta ψ G b‖ ≤ Real.sqrt (2 * (C₀ * n) * Real.log (q / n)) := by
    intro b
    refine le_trans (hpt b) ?_
    apply Real.sqrt_le_sqrt
    have hlog := log_div_pred_le_log_div (q := q) (n := n) hn hq
    nlinarith [hC, hlog]
  apply Finset.sup'_le
  intro b _
  exact hlift b

end ArkLib.ProximityGap.I031MFromPointwise

/-! ## Axiom audit -/
open ArkLib.ProximityGap.I031MFromPointwise in
#print axioms forall_mem_periodMagnitudes_iff_forall_norm_eta
open ArkLib.ProximityGap.I031MFromPointwise in
#print axioms i031_M_le_logTarget_of_pointwise
