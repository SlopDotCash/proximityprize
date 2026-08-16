/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Power-saving exponent gate for subgroup exponential-sum inputs

Local BGK / Bourgain--Chang / Kowalski / di Benedetto style inputs for multiplicative subgroups
often have the shape

`|sum_{x in H} psi(a x)| <= C * |H| * p^{-nu}`.

At the #464 prize diagonal `p = n^beta`, with `n = |H|`, this has `n`-exponent

`1 - beta * nu`.

The prize target, up to logarithms and constants, is `n^(1/2)`.  This file records the exact
exponent bookkeeping: the `p^{-nu}` saving reaches the prize scale only when

`nu >= 1 / (2 * beta)`.

At the binding beta-four diagonal this is `nu >= 1/8`.  The file proves only the arithmetic
contract.  It does not assert any BGK theorem or any value of `nu`.
-/

namespace ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate

/-- The `n`-exponent produced by a subgroup exponential-sum theorem of the form
`|H| * p^{-nu}` when the field scale is `p = n^beta`. -/
noncomputable def nExponentFromPSaving (beta nu : ℝ) : ℝ :=
  1 - beta * nu

/-- The prize exponent, ignoring logarithmic and constant factors. -/
noncomputable def prizeNExponent : ℝ :=
  1 / 2

/-- Required `p`-saving exponent at field-scale exponent `beta`. -/
noncomputable def requiredPSaving (beta : ℝ) : ℝ :=
  1 / (2 * beta)

/-- Exact exponent threshold: a `|H| * p^{-nu}` theorem reaches the `sqrt |H|` exponent at
`p = n^beta` precisely when `nu >= 1 / (2*beta)`. -/
theorem pSaving_reaches_prize_iff {beta nu : ℝ} (hbeta : 0 < beta) :
    nExponentFromPSaving beta nu ≤ prizeNExponent ↔ requiredPSaving beta ≤ nu := by
  unfold nExponentFromPSaving prizeNExponent requiredPSaving
  have h2beta : (0 : ℝ) < 2 * beta := by linarith
  constructor
  · intro h
    rw [div_le_iff₀ h2beta]
    nlinarith
  · intro h
    have hmul : (1 : ℝ) ≤ nu * (2 * beta) := by
      exact (div_le_iff₀ h2beta).mp h
    nlinarith

/-- Complementary strict form: if the `p`-saving exponent is below `1/(2*beta)`, the resulting
`n`-exponent is still strictly above the prize `1/2` exponent. -/
theorem pSaving_misses_prize_iff {beta nu : ℝ} (hbeta : 0 < beta) :
    prizeNExponent < nExponentFromPSaving beta nu ↔ nu < requiredPSaving beta := by
  unfold nExponentFromPSaving prizeNExponent requiredPSaving
  have h2beta : (0 : ℝ) < 2 * beta := by linarith
  constructor
  · intro h
    rw [lt_div_iff₀ h2beta]
    nlinarith
  · intro h
    have hmul : nu * (2 * beta) < (1 : ℝ) := by
      exact (lt_div_iff₀ h2beta).mp h
    nlinarith

/-- At the beta-four prize diagonal, the required `p`-saving is exactly one eighth. -/
theorem requiredPSaving_beta_four :
    requiredPSaving 4 = (1 / 8 : ℝ) := by
  norm_num [requiredPSaving]

/-- Beta-four consumer form: `|H| * p^{-nu}` can reach the prize exponent only when
`nu >= 1/8`. -/
theorem pSaving_reaches_prize_beta_four (nu : ℝ) :
    nExponentFromPSaving 4 nu ≤ prizeNExponent ↔ (1 / 8 : ℝ) ≤ nu := by
  simpa [requiredPSaving_beta_four] using
    (pSaving_reaches_prize_iff (beta := 4) (nu := nu) (by norm_num : (0 : ℝ) < 4))

/-- Beta-four strict obstruction form: any `p^{-nu}` theorem with `nu < 1/8` still lands above the
`sqrt |H|` exponent. -/
theorem pSaving_misses_prize_beta_four (nu : ℝ) :
    prizeNExponent < nExponentFromPSaving 4 nu ↔ nu < (1 / 8 : ℝ) := by
  simpa [requiredPSaving_beta_four] using
    (pSaving_misses_prize_iff (beta := 4) (nu := nu) (by norm_num : (0 : ℝ) < 4))

/-- The beta-four threshold is much larger than the small illustrative saving `11/1000`
used elsewhere to record the proven SOTA scale. -/
theorem eleven_over_thousand_lt_beta_four_required :
    (11 / 1000 : ℝ) < requiredPSaving 4 := by
  norm_num [requiredPSaving]

end ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.pSaving_reaches_prize_iff
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.pSaving_misses_prize_iff
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.requiredPSaving_beta_four
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.pSaving_reaches_prize_beta_four
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.pSaving_misses_prize_beta_four
#print axioms ArkLib.ProximityGap.Frontier.SubgroupExpSumPSavingGate.eleven_over_thousand_lt_beta_four_required
