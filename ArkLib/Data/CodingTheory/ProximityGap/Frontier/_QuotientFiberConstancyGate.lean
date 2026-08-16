/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._QuotientTailSupConsumer

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Quotient tail bounds need a pullback/fiber-constancy hypothesis

`_QuotientTailSupConsumer` proves the exact atom-scale gate for a score `Y : Q -> ℝ` on a finite
quotient.  This file records the adjacent bookkeeping condition needed before such a quotient
estimate can control an original score `X : α -> ℝ`.

The safe consumers are:

* `X` factors through the quotient score `Y`; or
* `X` is bounded above by the pullback of `Y` up to an error `Delta`; or
* representative bounds plus a fiber-oscillation bound control every point in each fiber.

The obstruction is equally finite: on the one-point quotient, the quotient score can have perfect
tail mass while the original score has a hidden spike inside the fiber.  Thus a dilation-quotient
tail estimate is not a full-frequency sup estimate until the pullback/fiber-control hypothesis is
part of the theorem.
-/

open ArkLib.ProximityGap.Frontier.QuotientTailSupConsumer

namespace ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate

variable {α Q : Type}

/-! ## Pullback and fiber-control interfaces -/

/-- The original score is exactly the pullback of a quotient score. -/
def FactorsThroughBy (quot : α -> Q) (X : α -> ℝ) (Y : Q -> ℝ) : Prop :=
  ∀ a : α, X a = Y (quot a)

/-- The original score factors through some quotient score. -/
def FactorsThrough (quot : α -> Q) (X : α -> ℝ) : Prop :=
  ∃ Y : Q -> ℝ, FactorsThroughBy quot X Y

/-- One-sided pullback control with additive loss `Delta`. -/
def PullbackUpper (quot : α -> Q) (X : α -> ℝ) (Y : Q -> ℝ) (Delta : ℝ) : Prop :=
  ∀ a : α, X a ≤ Y (quot a) + Delta

/-- A one-sided oscillation bound inside every quotient fiber. -/
def FiberUpperOscillation (quot : α -> Q) (X : α -> ℝ) (Delta : ℝ) : Prop :=
  ∀ a a' : α, quot a = quot a' -> X a ≤ X a' + Delta

/-- If `X` factors through a bounded quotient score, then `X` is bounded. -/
theorem forall_le_of_factorsThroughBy_and_quotient_bound
    (quot : α -> Q) {X : α -> ℝ} {Y : Q -> ℝ} {T : ℝ}
    (hfac : FactorsThroughBy quot X Y)
    (hY : ∀ q : Q, Y q ≤ T) :
    ∀ a : α, X a ≤ T := by
  intro a
  rw [hfac a]
  exact hY (quot a)

/-- Pullback control with loss `Delta` transports a quotient sup bound to the original score. -/
theorem forall_le_add_of_pullbackUpper_and_quotient_bound
    (quot : α -> Q) {X : α -> ℝ} {Y : Q -> ℝ} {T Delta : ℝ}
    (hpull : PullbackUpper quot X Y Delta)
    (hY : ∀ q : Q, Y q ≤ T) :
    ∀ a : α, X a ≤ T + Delta := by
  intro a
  calc
    X a ≤ Y (quot a) + Delta := hpull a
    _ ≤ T + Delta := by
      simpa [add_comm] using add_le_add_right (hY (quot a)) Delta

/-- A quotient tail estimate plus exact factorization gives a full-score pointwise bound. -/
theorem forall_le_of_quotientTailMass_and_factorsThroughBy
    [Fintype Q] [Nonempty Q]
    (quot : α -> Q) {X : α -> ℝ} {Y : Q -> ℝ} {T U : ℝ}
    (hfac : FactorsThroughBy quot X Y)
    (hmass : quotientTailMass Y T ≤ U)
    (hcardU : (Fintype.card Q : ℝ) * U < 1) :
    ∀ a : α, X a ≤ T :=
  forall_le_of_factorsThroughBy_and_quotient_bound quot hfac
    (fun q => pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
      (α := Q) (Q := Q) (fun q' : Q => q') (Y := Y) (T := T) (U := U) hmass hcardU q)

/-- A quotient tail estimate plus one-sided pullback control gives a full-score pointwise bound
with the same additive loss. -/
theorem forall_le_add_of_quotientTailMass_and_pullbackUpper
    [Fintype Q] [Nonempty Q]
    (quot : α -> Q) {X : α -> ℝ} {Y : Q -> ℝ} {T U Delta : ℝ}
    (hpull : PullbackUpper quot X Y Delta)
    (hmass : quotientTailMass Y T ≤ U)
    (hcardU : (Fintype.card Q : ℝ) * U < 1) :
    ∀ a : α, X a ≤ T + Delta :=
  forall_le_add_of_pullbackUpper_and_quotient_bound quot hpull
    (fun q => pulledBack_forall_le_of_quotientTailMass_bound_card_mul_lt_one
      (α := Q) (Q := Q) (fun q' : Q => q') (Y := Y) (T := T) (U := U) hmass hcardU q)

/-- Representative bounds plus a fiber-oscillation estimate control the whole original score. -/
theorem forall_le_add_of_representative_bound_and_fiberOscillation
    (quot : α -> Q) (rep : Q -> α) {X : α -> ℝ} {T Delta : ℝ}
    (hrep : ∀ q : Q, quot (rep q) = q)
    (hosc : FiberUpperOscillation quot X Delta)
    (hrepBound : ∀ q : Q, X (rep q) ≤ T) :
    ∀ a : α, X a ≤ T + Delta := by
  intro a
  calc
    X a ≤ X (rep (quot a)) + Delta := hosc a (rep (quot a)) (hrep (quot a)).symm
    _ ≤ T + Delta := by
      simpa [add_comm] using add_le_add_right (hrepBound (quot a)) Delta

/-! ## Hidden-fiber spike obstruction -/

/-- A singleton spike on the original domain. -/
def pointSpike [DecidableEq α] (a₀ : α) (base high : ℝ) : α -> ℝ :=
  fun a : α => if a = a₀ then high else base

/-- The one-point quotient score has zero strict tail at its own value. -/
theorem quotientTailMass_unit_const (T : ℝ) :
    quotientTailMass (fun _ : PUnit => T) T = 0 := by
  classical
  unfold quotientTailMass quotientTailCount
  simp

/-- A perfectly bounded one-point quotient score is compatible with a hidden full-score spike if no
pullback/fiber-control hypothesis links the full score to the quotient score. -/
theorem unitQuotient_tail_zero_allows_hidden_full_spike
    [Nonempty α]
    {T high Delta U : ℝ}
    (hU : 0 ≤ U)
    (hspike : T < high)
    (hhigh : T + Delta < high) :
    ∃ X : α -> ℝ, ∃ Y : PUnit -> ℝ, ∃ quot : α -> PUnit,
      quotientTailMass Y T ≤ U ∧
      (∀ q : PUnit, Y q ≤ T) ∧
      ¬ PullbackUpper quot X Y Delta ∧
      ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  refine ⟨pointSpike a₀ T high, fun _ : PUnit => T, fun _ : α => PUnit.unit, ?_, ?_, ?_, ?_⟩
  · simpa [quotientTailMass_unit_const] using hU
  · intro q
    rfl
  · intro hpull
    have hle : high ≤ T + Delta := by
      simpa [PullbackUpper, pointSpike, a₀] using hpull a₀
    exact not_lt_of_ge hle hhigh
  · exact ⟨a₀, by simpa [pointSpike, a₀] using hspike⟩

/-- Simpler obstruction form: a bounded quotient score alone does not force a pointwise bound on an
unrelated original score. -/
theorem unitQuotient_bound_not_force_fullScore
    [Nonempty α] {T high : ℝ}
    (hhigh : T < high) :
    ∃ X : α -> ℝ, ∃ Y : PUnit -> ℝ, ∃ quot : α -> PUnit,
      (∀ a : α, quot a = PUnit.unit) ∧
      (∀ q : PUnit, Y q ≤ T) ∧
      ∃ a : α, T < X a := by
  classical
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  refine ⟨pointSpike a₀ T high, fun _ : PUnit => T, fun _ : α => PUnit.unit, ?_, ?_, ?_⟩
  · intro a
    rfl
  · intro q
    rfl
  · exact ⟨a₀, by simpa [pointSpike, a₀] using hhigh⟩

end ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.forall_le_of_factorsThroughBy_and_quotient_bound
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.forall_le_add_of_pullbackUpper_and_quotient_bound
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.forall_le_of_quotientTailMass_and_factorsThroughBy
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.forall_le_add_of_quotientTailMass_and_pullbackUpper
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.forall_le_add_of_representative_bound_and_fiberOscillation
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.quotientTailMass_unit_const
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.unitQuotient_tail_zero_allows_hidden_full_spike
#print axioms ArkLib.ProximityGap.Frontier.QuotientFiberConstancyGate.unitQuotient_bound_not_force_fullScore
