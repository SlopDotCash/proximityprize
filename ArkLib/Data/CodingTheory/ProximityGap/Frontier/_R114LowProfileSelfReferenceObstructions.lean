/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._LowProfileFiberBound

/-!
# Obstructions to the self-referential low-profile fiber closure

`_LowProfileFiberBound.lean` shows that the per-scalar exact-fiber route only gives a circular
input: exact fibers are bounded by the same line's bad-scalar count.  This file packages the
audit-facing negative forms: on a nontrivial large-zero line, a constant self-referential fiber
budget cannot fit into any output budget below the input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

namespace ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions

open ProximityGap.LowProfileFiber
open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
/-- A self-referential constant fiber fit forces an expanding output budget. -/
theorem selfReferential_constant_fit_forces_output_ge
    {a B Λ : ℕ} (ha : 1 ≤ a) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hFits : ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ)) :
    a * (Λ * (directionSupportSet u₁).card) ≤ B :=
  selfReferential_fiberFit_forces ha u₁ hz hFits

open Classical in
/-- Contrapositive scanner form: if the output budget is smaller than the forced expansion,
then the constant self-referential fiber fit cannot hold. -/
theorem not_selfReferential_constant_fit_of_output_lt_forced
    {a B Λ : ℕ} (ha : 1 ≤ a) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hlt : B < a * (Λ * (directionSupportSet u₁).card)) :
    ¬ ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ) := by
  intro hFits
  exact (Nat.not_le.mpr hlt) (selfReferential_fiberFit_forces ha u₁ hz hFits)

open Classical in
/-- Fixed-point obstruction package: on a large-zero line with nonempty moving support and
`a ≥ 2`, no constant self-referential fit can have output budget `B ≤ Λ`. -/
theorem not_selfReferential_constant_fit_at_or_below_input
    {a B Λ : ℕ} (ha : 2 ≤ a) (hΛ : 1 ≤ Λ) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hs : 1 ≤ (directionSupportSet u₁).card)
    (hB : B ≤ Λ) :
    ¬ ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ) := by
  intro hFits
  exact no_selfReferential_fiberFit_fixedPoint ha hΛ u₁ hz hs hFits hB

open Classical in
/-- Strict self-improvement is impossible: the same obstruction applies a fortiori when
`B < Λ`. -/
theorem not_selfReferential_constant_fit_below_input
    {a B Λ : ℕ} (ha : 2 ≤ a) (hΛ : 1 ≤ Λ) (u₁ : Fin n → F)
    (hz : ¬ SupportEligibleLineDirection a u₁)
    (hs : 1 ≤ (directionSupportSet u₁).card)
    (hB : B < Λ) :
    ¬ ZeroCoordinateAgreementFiberBudgetFits (F := F) (n := n) a B u₁ (fun _ => Λ) :=
  not_selfReferential_constant_fit_at_or_below_input ha hΛ u₁ hz hs hB.le

open Classical in
/-- Uniform-safe-fit obstruction: if one nontrivial large-zero direction exists, then the
constant self-referential envelope cannot be a uniform large-zero-safe fit at or below its
own input budget.  This is the assembled-weld version of
`not_selfReferential_constant_fit_at_or_below_input`. -/
theorem not_uniform_selfReferential_constant_fit_at_or_below_input
    {a B Λ : ℕ} (ha : 2 ≤ a) (hΛ : 1 ≤ Λ)
    (u₁ : Fin n → F) (hz : ¬ SupportEligibleLineDirection a u₁)
    (hs : 1 ≤ (directionSupportSet u₁).card) (hB : B ≤ Λ) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits
        (F := F) (n := n) a B (fun _ => Λ) := by
  intro hFits
  exact not_selfReferential_constant_fit_at_or_below_input ha hΛ u₁ hz hs hB
    (hFits u₁ hz)

open Classical in
/-- Strict uniform self-improvement is impossible for the same reason. -/
theorem not_uniform_selfReferential_constant_fit_below_input
    {a B Λ : ℕ} (ha : 2 ≤ a) (hΛ : 1 ≤ Λ)
    (u₁ : Fin n → F) (hz : ¬ SupportEligibleLineDirection a u₁)
    (hs : 1 ≤ (directionSupportSet u₁).card) (hB : B < Λ) :
    ¬ UniformLargeZeroSafeCoordinateAgreementFiberBudgetFits
        (F := F) (n := n) a B (fun _ => Λ) :=
  not_uniform_selfReferential_constant_fit_at_or_below_input ha hΛ u₁ hz hs hB.le

end ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions

/-! ## Axiom audit -/
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.selfReferential_constant_fit_forces_output_ge
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.not_selfReferential_constant_fit_of_output_lt_forced
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.not_selfReferential_constant_fit_at_or_below_input
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.not_selfReferential_constant_fit_below_input
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.not_uniform_selfReferential_constant_fit_at_or_below_input
#print axioms
  ProximityGap.LowProfileFiber.Frontier.R114LowProfileSelfReferenceObstructions.not_uniform_selfReferential_constant_fit_below_input
