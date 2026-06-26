/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Quadratic Vinogradov bounds control the wrong system unless a transfer theorem is supplied

The finite-field quadratic Vinogradov mean-value theorem bounds solutions to the simultaneous
linear-plus-quadratic balance system

```text
sum_i (x_i - y_i) = 0
sum_i (x_i^2 - y_i^2) = 0.
```

The #464 period moment counts only the linear balance.  A saving for the stricter quadratic system
therefore does not bound the linear energy unless one also proves a transfer theorem saying that the
linear solutions relevant to `mu_n` automatically satisfy the added quadratic equation, or are
otherwise covered by the quadratic system at the needed scale.

This file records that logical gate abstractly.  It proves the positive consumer with the missing
transfer hypothesis, and a finite countermodel showing that a bound on the strict system alone can
hold while the linear count is arbitrarily larger than the target.
-/

namespace ArkLib.ProximityGap.Frontier.QuadraticVinogradovWrongSystemGate

/-- Count the elements of a finite ambient configuration type satisfying `P`. -/
noncomputable def countWhere {Ω : Type} [Fintype Ω] (P : Ω -> Prop) : ℕ :=
  Nat.card {ω : Ω // P ω}

/-- A target bound on the linear-balance count. -/
def LinearEnergyBound {Ω : Type} [Fintype Ω] (Linear : Ω -> Prop) (B : ℕ) : Prop :=
  countWhere Linear <= B

/-- A target bound on the stricter linear-plus-quadratic system. -/
def QuadraticSystemBound {Ω : Type} [Fintype Ω]
    (Linear Quadratic : Ω -> Prop) (B : ℕ) : Prop :=
  countWhere (fun ω : Ω => Linear ω ∧ Quadratic ω) <= B

/-- The missing transfer theorem: every relevant linear solution satisfies the added quadratic
constraint.  In the actual #464 application this is exactly the nontrivial step a quadratic-VMVT
route would have to supply. -/
def ExtraEquationComplete {Ω : Type} (Linear Quadratic : Ω -> Prop) : Prop :=
  ∀ ω : Ω, Linear ω -> Quadratic ω

/-- A witness satisfying the original linear balance but not the added quadratic constraint. -/
def LinearOnlyWitness {Ω : Type} (Linear Quadratic : Ω -> Prop) : Prop :=
  ∃ ω : Ω, Linear ω ∧ ¬ Quadratic ω

/-- The extra-equation transfer theorem is exactly absence of a linear-only witness. -/
theorem extraEquationComplete_iff_no_linearOnlyWitness {Ω : Type}
    (Linear Quadratic : Ω -> Prop) :
    ExtraEquationComplete Linear Quadratic ↔ ¬ LinearOnlyWitness Linear Quadratic := by
  constructor
  · intro hcomplete hbad
    rcases hbad with ⟨ω, hlin, hnotquad⟩
    exact hnotquad (hcomplete ω hlin)
  · intro hno ω hlin
    by_contra hnotquad
    exact hno ⟨ω, hlin, hnotquad⟩

/-- The strict system is always a subset of the linear system.  This is the direction supplied for
free by adding equations; it is not the direction needed to bound the linear energy. -/
theorem strict_count_le_linear_count {Ω : Type} [Fintype Ω]
    (Linear Quadratic : Ω -> Prop) :
    countWhere (fun ω : Ω => Linear ω ∧ Quadratic ω) <= countWhere Linear := by
  unfold countWhere
  exact Nat.card_le_card_of_injective
    (fun ω : {ω : Ω // Linear ω ∧ Quadratic ω} =>
      (⟨ω.1, ω.2.1⟩ : {ω : Ω // Linear ω}))
    (by
      intro x y hxy
      exact Subtype.ext
        (show x.1 = y.1 from
          congrArg (fun z : {ω : Ω // Linear ω} => z.1) hxy))

/-- If the added quadratic equation is complete on the relevant linear solutions, then the strict
count equals the linear count. -/
theorem strict_count_eq_linear_count_of_extra_complete {Ω : Type} [Fintype Ω]
    (Linear Quadratic : Ω -> Prop)
    (hcomplete : ExtraEquationComplete Linear Quadratic) :
    countWhere (fun ω : Ω => Linear ω ∧ Quadratic ω) = countWhere Linear := by
  unfold countWhere
  exact Nat.card_congr
    { toFun := fun ω => (⟨ω.1, ω.2.1⟩ : {ω : Ω // Linear ω})
      invFun := fun ω =>
        (⟨ω.1, ⟨ω.2, hcomplete ω.1 ω.2⟩⟩ :
          {ω : Ω // Linear ω ∧ Quadratic ω})
      left_inv := by
        intro ω
        exact Subtype.ext rfl
      right_inv := by
        intro ω
        exact Subtype.ext rfl }

/-- Positive consumer: a quadratic-system bound gives the desired linear-energy bound only after
the extra-equation completeness theorem. -/
theorem linear_bound_of_quadratic_bound_and_extra_complete {Ω : Type} [Fintype Ω]
    (Linear Quadratic : Ω -> Prop) {B : ℕ}
    (hquad : QuadraticSystemBound Linear Quadratic B)
    (hcomplete : ExtraEquationComplete Linear Quadratic) :
    LinearEnergyBound Linear B := by
  unfold LinearEnergyBound QuadraticSystemBound at *
  rw [← strict_count_eq_linear_count_of_extra_complete Linear Quadratic hcomplete]
  exact hquad

/-- Equivalent positive consumer in witness form: a quadratic-system bound controls the original
linear energy only after ruling out linear-only witnesses. -/
theorem linear_bound_of_quadratic_bound_and_no_linearOnlyWitness
    {Ω : Type} [Fintype Ω]
    (Linear Quadratic : Ω -> Prop) {B : ℕ}
    (hquad : QuadraticSystemBound Linear Quadratic B)
    (hno : ¬ LinearOnlyWitness Linear Quadratic) :
    LinearEnergyBound Linear B :=
  linear_bound_of_quadratic_bound_and_extra_complete Linear Quadratic hquad
    ((extraEquationComplete_iff_no_linearOnlyWitness Linear Quadratic).mpr hno)

/-- Countermodel: a strict-system bound alone does not force a linear-energy bound.  Take every
ambient configuration to satisfy the linear equation and none to satisfy the added quadratic
equation.  Then the quadratic count is zero, while the linear count is the whole ambient size. -/
theorem quadratic_bound_not_force_linear_bound {Ω : Type} [Fintype Ω] {B : ℕ}
    (hB : B < Fintype.card Ω) :
    ∃ Linear Quadratic : Ω -> Prop,
      QuadraticSystemBound Linear Quadratic B ∧ ¬ LinearEnergyBound Linear B := by
  classical
  refine ⟨(fun _ : Ω => True), (fun _ : Ω => False), ?_, ?_⟩
  · unfold QuadraticSystemBound countWhere
    simp
  · unfold LinearEnergyBound countWhere
    simp [hB.not_ge]

/-- Packaged gate: the available direct implication is strict-to-linear only under the transfer
hypothesis; without it, a finite model can satisfy the strict-system bound and fail the linear one. -/
theorem quadraticVinogradov_wrongSystem_gate {Ω : Type} [Fintype Ω] {B : ℕ}
    (hB : B < Fintype.card Ω) :
    (∀ Linear Quadratic : Ω -> Prop,
        QuadraticSystemBound Linear Quadratic B ->
        ExtraEquationComplete Linear Quadratic ->
        LinearEnergyBound Linear B)
      ∧
    ∃ Linear Quadratic : Ω -> Prop,
      QuadraticSystemBound Linear Quadratic B ∧ ¬ LinearEnergyBound Linear B := by
  constructor
  · intro Linear Quadratic hquad hcomplete
    exact linear_bound_of_quadratic_bound_and_extra_complete Linear Quadratic hquad hcomplete
  · exact quadratic_bound_not_force_linear_bound hB

/-! ## Axiom audit -/
#print axioms extraEquationComplete_iff_no_linearOnlyWitness
#print axioms strict_count_le_linear_count
#print axioms strict_count_eq_linear_count_of_extra_complete
#print axioms linear_bound_of_quadratic_bound_and_extra_complete
#print axioms linear_bound_of_quadratic_bound_and_no_linearOnlyWitness
#print axioms quadratic_bound_not_force_linear_bound
#print axioms quadraticVinogradov_wrongSystem_gate

end ArkLib.ProximityGap.Frontier.QuadraticVinogradovWrongSystemGate
