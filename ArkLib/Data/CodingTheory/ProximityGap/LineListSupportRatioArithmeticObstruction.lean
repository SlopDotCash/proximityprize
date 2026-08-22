/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineListArithmeticObstruction
import ArkLib.Data.CodingTheory.ProximityGap.LineListSupportRatioFiber

/-!
# Arithmetic obstruction for the support-ratio line-cover envelope

`LineListSupportRatioFiber.lean` turns exact appearance into the support-ratio line-cover
envelope

```text
M t = |F| * choose(n, a - t).
```

This file records the matching arithmetic no-go surface: the weighted binomial fit contains every
individual `t` summand, so a single over-budget zero/support profile refutes the ambient
line-cover envelope.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- If the moving support covers `a - t`, the ambient support-ratio line-cover fit already
forces the unweighted scalar-times-binomial `t` term under budget. -/
theorem lineFiberCoverChooseBudgetFits_choose_le_of_support_ge_sub
    (a B t : ℕ) (u₁ : Fin n → F) (ht : t < a)
    (hsupport : a - t ≤ (directionSupportSet u₁).card)
    (hFits : ZeroAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B u₁
      (fun t => Fintype.card F * n.choose (a - t))) :
    (directionZeroSet u₁).card.choose t * (Fintype.card F * n.choose (a - t)) ≤ B := by
  have hterm :=
    lineFiberCoverChooseBudgetFits_term_le
      (F := F) (n := n) a B t u₁ ht hFits
  have hdenpos : 0 < a - t := Nat.sub_pos_of_lt ht
  have hdiv : 1 ≤ (directionSupportSet u₁).card / (a - t) :=
    Nat.div_pos hsupport hdenpos
  have hmono :
      (directionZeroSet u₁).card.choose t * (Fintype.card F * n.choose (a - t))
        ≤ ((directionZeroSet u₁).card.choose t *
            (Fintype.card F * n.choose (a - t))) *
          ((directionSupportSet u₁).card / (a - t)) := by
    exact Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one hdiv)
  exact le_trans hmono hterm

/-- A large-zero direction whose support covers `a - t` and whose ambient line-cover `t` term
already exceeds `B` refutes the uniform appearance-fiber fit. -/
theorem
    not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_exists_choose_gt
    (a B : ℕ)
    (hgt : ∃ u₁ : Fin n → F, ¬ SupportEligibleLineDirection a u₁ ∧
      ∃ t : ℕ, t < a ∧ a - t ≤ (directionSupportSet u₁).card ∧
        B < (directionZeroSet u₁).card.choose t *
          (Fintype.card F * n.choose (a - t))) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F * n.choose (a - t)) := by
  intro hFits
  rcases hgt with ⟨u₁, hnotEligible, t, ht, hsupport, hgt⟩
  exact (not_lt_of_ge
    (lineFiberCoverChooseBudgetFits_choose_le_of_support_ge_sub
      (F := F) (n := n) a B t u₁ ht hsupport (hFits u₁ hnotEligible))) hgt

open Classical in
/-- Parameter-only obstruction for the ambient support-ratio line-cover envelope.  If a possible
large-zero direction can have `z` zero coordinates and still has enough moving support to activate
the `t` summand, then the ambient line-cover fit forces
`choose(z, t) * |F| * choose(n, a - t) ≤ B`. -/
theorem not_lineFiberCoverChooseFit_of_zeroCount_choose_gt
    (a B z t : ℕ) (hz : z ≤ n) (hlarge : a ≤ z) (ht : t < a)
    (hsupport : a - t ≤ n - z)
    (hB : B < z.choose t * (Fintype.card F * n.choose (a - t))) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F * n.choose (a - t)) := by
  rcases exists_direction_zero_card_eq_support_card_eq (F := F) (n := n) z hz with
    ⟨u₁, hzero, hsupportCard⟩
  exact
    not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_exists_choose_gt
      (F := F) (n := n) a B
      ⟨u₁, by
        rw [SupportEligibleLineDirection, hzero]
        exact not_lt_of_ge hlarge,
        t, ht, by
          rw [hsupportCard]
          exact hsupport,
        by
          rw [hzero]
          exact hB⟩

open Classical in
/-- In the common `2a ≤ n` range, the ambient support-ratio line-cover arithmetic fit is
impossible for any target below `|F| * choose(n, a)`. -/
theorem
    not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_two_mul_le
    (a B : ℕ) (ha : 0 < a) (h2a : 2 * a ≤ n)
    (hB : B < Fintype.card F * n.choose a) :
    ¬ UniformLargeZeroSafeAppearingCoordinateFiberBudgetFits (F := F) (n := n) a B
      (fun t => Fintype.card F * n.choose (a - t)) := by
  have ha_le_n : a ≤ n := by omega
  exact not_lineFiberCoverChooseFit_of_zeroCount_choose_gt
    (F := F) (n := n) a B a 0 ha_le_n le_rfl ha
    (by omega)
    (by simpa)

section SourceAudit

#print axioms zeroAppearingCoordinateFiberBudgetFits_term_le
#print axioms lineFiberCoverChooseBudgetFits_term_le
#print axioms lineFiberCoverChooseBudgetFits_choose_le_of_support_ge_sub
#print axioms
  not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_exists_choose_gt
#print axioms not_lineFiberCoverChooseFit_of_zeroCount_choose_gt
#print axioms
  not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_two_mul_le

end SourceAudit

end ProximityGap.Ownership
