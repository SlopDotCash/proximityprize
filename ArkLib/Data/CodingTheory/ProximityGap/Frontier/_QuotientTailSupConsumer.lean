/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Quotient tail bounds and the correct union-bound atom count

`_VerticalTailSupConsumer` records the atom-scale gate for distributional tail estimates.  This file
adds the quotient form needed for the dilation-orbit face of issue #464.

If a score on a full frequency set factors through a finite quotient

`quot : α -> Q`, `Y : Q -> ℝ`,

then the pointwise bound on the full set follows from a tail estimate on the quotient once the
quotient tail mass is below `1 / #Q`.  This is the formal reason the dilation quotient can replace
`log p` by `log m = log((p-1)/n)` in a genuine union-bound argument.

The converse is also recorded: any quotient-tail budget at or above one quotient atom is compatible
with a score spike on one quotient class, and hence with a bad full frequency in its preimage.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer

variable {α Q : Type} [Fintype Q]

/-- Number of quotient atoms whose score is strictly above threshold `T`. -/
noncomputable def quotientTailCount (Y : Q -> ℝ) (T : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun q => T < Y q)).card

/-- Uniform empirical tail mass on the quotient. -/
noncomputable def quotientTailMass (Y : Q -> ℝ) (T : ℝ) : ℝ :=
  (quotientTailCount Y T : ℝ) / (Fintype.card Q : ℝ)

/-- A quotient tail bound below one quotient atom gives a pointwise bound on the quotient. -/
theorem quotient_forall_le_of_tailMass_lt_inv_card
    {Y : Q -> ℝ} {T : ℝ}
    (hsmall : quotientTailMass Y T < (1 : ℝ) / (Fintype.card Q : ℝ)) :
    ∀ q : Q, Y q ≤ T := by
  classical
  intro q
  exact le_of_not_gt (fun hgt => by
    have hden_nonneg : (0 : ℝ) ≤ (Fintype.card Q : ℝ) := by positivity
    have hcount_nat : 1 ≤ quotientTailCount Y T := by
      unfold quotientTailCount
      exact Finset.one_le_card.mpr ⟨q, by simp [hgt]⟩
    have hcount : (1 : ℝ) ≤ (quotientTailCount Y T : ℝ) := by
      exact_mod_cast hcount_nat
    have hmass_ge : (1 : ℝ) / (Fintype.card Q : ℝ) ≤ quotientTailMass Y T := by
      unfold quotientTailMass
      exact div_le_div_of_nonneg_right hcount hden_nonneg
    exact (not_lt_of_ge hmass_ge) hsmall)

/-- A quotient tail upper bound below one quotient atom gives a pointwise bound on the quotient. -/
theorem quotient_forall_le_of_tailMass_bound_lt_inv_card
    {Y : Q -> ℝ} {T U : ℝ}
    (hmass : quotientTailMass Y T ≤ U)
    (hU : U < (1 : ℝ) / (Fintype.card Q : ℝ)) :
    ∀ q : Q, Y q ≤ T :=
  quotient_forall_le_of_tailMass_lt_inv_card (Y := Y) (T := T) (lt_of_le_of_lt hmass hU)

/-- Pulling back a quotient score, a below-one-atom quotient tail estimate gives the pointwise
bound on the full frequency set. -/
theorem pulledBack_forall_le_of_quotientTailMass_bound_lt_inv_card
    (quot : α -> Q) {Y : Q -> ℝ} {T U : ℝ}
    (hmass : quotientTailMass Y T ≤ U)
    (hU : U < (1 : ℝ) / (Fintype.card Q : ℝ)) :
    ∀ a : α, Y (quot a) ≤ T := by
  intro a
  exact quotient_forall_le_of_tailMass_bound_lt_inv_card (Y := Y) (T := T) hmass hU (quot a)

/-- Rate form of the one-quotient-atom condition: `#Q * U < 1` implies
`U < 1 / #Q`. -/
theorem quotientTailMass_lt_inv_card_of_card_mul_lt_one [Nonempty Q]
    {U : ℝ}
    (hcardU : (Fintype.card Q : ℝ) * U < 1) :
    U < (1 : ℝ) / (Fintype.card Q : ℝ) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  have hdiv := div_lt_div_of_pos_right hcardU hcard_pos
  have hcard_ne : (Fintype.card Q : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hleft : ((Fintype.card Q : ℝ) * U) / (Fintype.card Q : ℝ) = U := by
    field_simp [hcard_ne]
  rwa [hleft] at hdiv

/-- Practical rate-gate consumer: a quotient-tail estimate with `#Q * U < 1` gives the pointwise
bound after pulling back to the full frequency set. -/
theorem pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one [Nonempty Q]
    (quot : α -> Q) {Y : Q -> ℝ} {T U : ℝ}
    (hmass : quotientTailMass Y T ≤ U)
    (hcardU : (Fintype.card Q : ℝ) * U < 1) :
    ∀ a : α, Y (quot a) ≤ T :=
  pulledBack_forall_le_of_quotientTailMass_bound_lt_inv_card
    quot hmass (quotientTailMass_lt_inv_card_of_card_mul_lt_one (Q := Q) hcardU)

/-- A singleton quotient spike has quotient tail mass exactly one quotient atom. -/
theorem quotientTailMass_single_spike [DecidableEq Q] (q₀ : Q) (T : ℝ) :
    quotientTailMass (fun q : Q => if q = q₀ then T + 1 else T) T
      = (1 : ℝ) / (Fintype.card Q : ℝ) := by
  classical
  have hfilter :
      (Finset.univ.filter (fun q : Q => T < if q = q₀ then T + 1 else T))
        = ({q₀} : Finset Q) := by
    ext q
    by_cases hq : q = q₀
    · simp [hq]
    · simp [hq]
  unfold quotientTailMass quotientTailCount
  rw [hfilter]
  simp

/-- Any quotient-tail budget at least one quotient atom is compatible with one full-frequency spike
whenever the full frequency set is nonempty. -/
theorem quotientTail_budget_allows_pulledBack_spike [Nonempty α] [DecidableEq Q]
    (quot : α -> Q) {T U : ℝ}
    (hU : (1 : ℝ) / (Fintype.card Q : ℝ) ≤ U) :
    ∃ Y : Q -> ℝ, quotientTailMass Y T ≤ U ∧ ∃ a : α, T < Y (quot a) := by
  classical
  let a₀ : α := Classical.choice ‹Nonempty α›
  let q₀ : Q := quot a₀
  refine ⟨fun q : Q => if q = q₀ then T + 1 else T, ?_, ⟨a₀, by simp [q₀]⟩⟩
  simpa [quotientTailMass_single_spike] using hU

/-- Rate form of the converse: `1 <= #Q * U` is still compatible with a pulled-back quotient
spike above threshold. -/
theorem quotientTail_budget_allows_pulledBack_spike_of_one_le_card_mul
    [Nonempty α] [Nonempty Q] [DecidableEq Q]
    (quot : α -> Q) {T U : ℝ}
    (hU : 1 ≤ (Fintype.card Q : ℝ) * U) :
    ∃ Y : Q -> ℝ, quotientTailMass Y T ≤ U ∧ ∃ a : α, T < Y (quot a) := by
  have hcard_pos : (0 : ℝ) < (Fintype.card Q : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty Q))
  have hdiv := div_le_div_of_nonneg_right hU (le_of_lt hcard_pos)
  have hcard_ne : (Fintype.card Q : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hright : ((Fintype.card Q : ℝ) * U) / (Fintype.card Q : ℝ) = U := by
    field_simp [hcard_ne]
  have hUinv : (1 : ℝ) / (Fintype.card Q : ℝ) ≤ U := by
    rwa [hright] at hdiv
  exact quotientTail_budget_allows_pulledBack_spike (α := α) quot (T := T) hUinv

/-- Exact atom-scale gate for quotient-tail estimates to imply pointwise bounds after pulling back
to the full frequency set.  The atom count is the quotient size `#Q`, not the full-set size. -/
theorem atomScaleGate_for_quotientTailSupBound [Nonempty α] [DecidableEq Q]
    (quot : α -> Q) {T U : ℝ} :
    (∀ Y : Q -> ℝ, quotientTailMass Y T ≤ U -> ∀ a : α, Y (quot a) ≤ T)
      ↔ U < (1 : ℝ) / (Fintype.card Q : ℝ) := by
  constructor
  · intro h
    by_contra hnot
    have hU : (1 : ℝ) / (Fintype.card Q : ℝ) ≤ U := le_of_not_gt hnot
    rcases quotientTail_budget_allows_pulledBack_spike (α := α) quot (T := T) hU with
      ⟨Y, hmass, a, hgt⟩
    exact (not_lt_of_ge (h Y hmass a)) hgt
  · intro hU Y hmass
    exact pulledBack_forall_le_of_quotientTailMass_bound_lt_inv_card
      (α := α) quot (Y := Y) (T := T) hmass hU

end ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotient_forall_le_of_tailMass_lt_inv_card
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotient_forall_le_of_tailMass_bound_lt_inv_card
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.pulledBack_forall_le_of_quotientTailMass_bound_lt_inv_card
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotientTailMass_lt_inv_card_of_card_mul_lt_one
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotientTailMass_single_spike
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotientTail_budget_allows_pulledBack_spike
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.quotientTail_budget_allows_pulledBack_spike_of_one_le_card_mul
#print axioms ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer.atomScaleGate_for_quotientTailSupBound
