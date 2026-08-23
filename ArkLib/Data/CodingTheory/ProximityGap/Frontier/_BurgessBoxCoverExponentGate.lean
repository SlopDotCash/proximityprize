/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Burgess-box cover exponent gate

Recent Burgess-type theorems for multiplicative character sums over additive boxes or sublattices
have the shape: an eligible box of volume `p^alpha` has cancellation saving `p^{-nu}`, hence the
box contribution is bounded at exponent `alpha - nu`.

Trying to use such a theorem for the #464 subgroup period has an extra transfer cost.  The prize
set has size `n = p^gamma` with `gamma = 1/4` at the binding beta-four diagonal, but a Burgess box
input is eligible only for volumes `p^(1/4 + epsilon)` (or analogous above-threshold volumes).
Any cover argument pays the cover-volume exponent `alpha`, not the subgroup exponent `gamma`.

This file records the exact arithmetic contract:

* a box-cover bound at exponent `alpha - nu` reaches the prize scale `p^(gamma/2)` iff
  `nu >= alpha - gamma/2`;
* at the binding subgroup exponent `gamma = 1/4` and eligible box exponent
  `alpha = 1/4 + epsilon`, the required saving is `1/8 + epsilon`;
* therefore a direct-subgroup saving threshold `1/8` is not enough for a box-cover transfer when
  `epsilon > 0`.

No Burgess theorem is assumed or proved here.  This is a routing guardrail for the PDF literature:
box/sublattice estimates need either a saving that pays the cover overhead, or a genuinely
measure-preserving transfer from the subgroup to eligible boxes.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.BurgessBoxCoverExponentGate

/-- The exponent of the target subgroup size `n = p^gamma`. -/
noncomputable def subgroupSizeExponent (gamma : ℝ) : ℝ :=
  gamma

/-- The prize exponent in `p`-scale: `sqrt(n) = p^(gamma/2)`, ignoring logarithms. -/
noncomputable def prizePExponent (gamma : ℝ) : ℝ :=
  gamma / 2

/-- A box-cover theorem over total eligible cover volume `p^alpha` with saving `p^{-nu}` gives
exponent `alpha - nu`. -/
noncomputable def boxCoverExponent (alpha nu : ℝ) : ℝ :=
  alpha - nu

/-- Required `p`-saving for a box-cover transfer to reach the subgroup prize exponent. -/
noncomputable def requiredBoxCoverSaving (gamma alpha : ℝ) : ℝ :=
  alpha - gamma / 2

/-- Exact threshold: a box-cover exponent reaches the prize scale iff the saving pays
`alpha - gamma/2`. -/
theorem boxCover_reaches_prize_iff {gamma alpha nu : ℝ} :
    boxCoverExponent alpha nu ≤ prizePExponent gamma ↔
      requiredBoxCoverSaving gamma alpha ≤ nu := by
  unfold boxCoverExponent prizePExponent requiredBoxCoverSaving
  constructor <;> intro h <;> linarith

/-- Strict complement: if the saving is below `alpha - gamma/2`, the cover-transfer exponent stays
above the prize exponent. -/
theorem boxCover_misses_prize_iff {gamma alpha nu : ℝ} :
    prizePExponent gamma < boxCoverExponent alpha nu ↔
      nu < requiredBoxCoverSaving gamma alpha := by
  unfold boxCoverExponent prizePExponent requiredBoxCoverSaving
  constructor <;> intro h <;> linarith

/-- Direct subgroup route at beta four has subgroup exponent `gamma = 1/4`, so the prize exponent
is `1/8`. -/
theorem prizePExponent_binding :
    prizePExponent (1 / 4 : ℝ) = 1 / 8 := by
  norm_num [prizePExponent]

/-- Eligible Burgess-box cover volume at the binding edge has exponent `1/4 + epsilon`; the required
saving is therefore `1/8 + epsilon`. -/
theorem requiredBoxCoverSaving_binding (epsilon : ℝ) :
    requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) = 1 / 8 + epsilon := by
  unfold requiredBoxCoverSaving
  ring

/-- Positive epsilon makes the box-cover saving requirement strictly stronger than the direct
subgroup `1/8` threshold. -/
theorem direct_threshold_lt_boxCover_required {epsilon : ℝ} (heps : 0 < epsilon) :
    (1 / 8 : ℝ) < requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) := by
  rw [requiredBoxCoverSaving_binding epsilon]
  linarith

/-- If a box-cover transfer at exponent `alpha = 1/4 + epsilon` has only the direct-subgroup
threshold saving `nu <= 1/8`, then it still misses the prize whenever `epsilon > 0`. -/
theorem binding_boxCover_misses_of_direct_saving_only
    {epsilon nu : ℝ} (heps : 0 < epsilon) (hnu : nu ≤ 1 / 8) :
    prizePExponent (1 / 4 : ℝ) <
      boxCoverExponent (1 / 4 + epsilon) nu := by
  have hreq : (1 / 8 : ℝ) < requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) :=
    direct_threshold_lt_boxCover_required heps
  have hmiss : nu < requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) := by
    linarith
  exact (boxCover_misses_prize_iff
    (gamma := (1 / 4 : ℝ)) (alpha := 1 / 4 + epsilon) (nu := nu)).2 hmiss

/-- If the saving pays `1/8 + epsilon`, the Burgess-box cover exponent reaches the prize exponent
at the binding edge. -/
theorem binding_boxCover_reaches_of_saving_pays_overhead
    {epsilon nu : ℝ} (hnu : 1 / 8 + epsilon ≤ nu) :
    boxCoverExponent (1 / 4 + epsilon) nu ≤ prizePExponent (1 / 4 : ℝ) := by
  have hreq : requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) ≤ nu := by
    rwa [requiredBoxCoverSaving_binding epsilon]
  exact (boxCover_reaches_prize_iff
    (gamma := (1 / 4 : ℝ)) (alpha := 1 / 4 + epsilon) (nu := nu)).2 hreq

/-- Packaged gate: at the binding diagonal, an eligible box-cover route with positive volume
overhead `epsilon` needs strictly more than the direct `1/8` saving; exactly paying
`1/8 + epsilon` is sufficient at exponent level. -/
theorem burgessBoxCoverExponentGate {epsilon : ℝ} (heps : 0 < epsilon) :
    (1 / 8 : ℝ) < requiredBoxCoverSaving (1 / 4 : ℝ) (1 / 4 + epsilon) ∧
    (∀ nu : ℝ, nu ≤ 1 / 8 →
      prizePExponent (1 / 4 : ℝ) < boxCoverExponent (1 / 4 + epsilon) nu) ∧
    (∀ nu : ℝ, 1 / 8 + epsilon ≤ nu →
      boxCoverExponent (1 / 4 + epsilon) nu ≤ prizePExponent (1 / 4 : ℝ)) := by
  refine ⟨direct_threshold_lt_boxCover_required heps, ?_, ?_⟩
  · intro nu hnu
    exact binding_boxCover_misses_of_direct_saving_only heps hnu
  · intro nu hnu
    exact binding_boxCover_reaches_of_saving_pays_overhead hnu

#print axioms boxCover_reaches_prize_iff
#print axioms boxCover_misses_prize_iff
#print axioms prizePExponent_binding
#print axioms requiredBoxCoverSaving_binding
#print axioms direct_threshold_lt_boxCover_required
#print axioms binding_boxCover_misses_of_direct_saving_only
#print axioms binding_boxCover_reaches_of_saving_pays_overhead
#print axioms burgessBoxCoverExponentGate

end ArkLib.ProximityGap.Frontier.BurgessBoxCoverExponentGate
