/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Collinear bad families charge injectively to mismatch coordinates

Suppose the selected decoded word for every bad scalar `gamma` lies on one fixed codeword
pencil `w0 + gamma * w1`.  The non-joint clause supplies a witness coordinate where the pair
`(w0,w1)` differs from the received pair `(u0,u1)`.  At such a coordinate the scalar agreement
equation determines `gamma` uniquely.  Choosing one mismatch coordinate per scalar therefore gives
an injection into the evaluation domain.

This is the correct collinear replacement for the false shared-fresh-triple exclusion: many
collinear events may share another fresh coordinate, but their non-joint mismatches are necessarily
distinct.  The result is parameter-free and gives the exact `#family <= block length` cap.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open _root_.ProximityGap

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCollinearMismatchCharge

variable {I F A : Type} [Fintype I] [DecidableEq I]
variable [Field F] [DecidableEq F]
variable [AddCommGroup A] [Module F A] [NoZeroSMulDivisors F A]

attribute [local instance] Classical.propDecidable

/-- A witness for `gamma` whose decoded word is the member `w0 + gamma * w1` of one fixed
codeword pencil.  The agreement threshold is irrelevant for the injection argument. -/
def CollinearWitnessAt (C : Set (I -> A)) (u0 u1 w0 w1 : I -> A) (gamma : F) : Prop :=
  exists S : Finset I,
    (forall x, x ∈ S -> w0 x + gamma • w1 x = u0 x + gamma • u1 x) ∧
      ¬ pairJointAgreesOn C S u0 u1

/-- Non-jointness forces every explaining codeword pair to mismatch the received pair somewhere
on the witness set. -/
theorem exists_pair_mismatch
    (C : Set (I -> A)) {S : Finset I} {u0 u1 w0 w1 : I -> A}
    (hw0 : w0 ∈ C) (hw1 : w1 ∈ C)
    (hno : ¬ pairJointAgreesOn C S u0 u1) :
    ∃ x ∈ S, w0 x ≠ u0 x ∨ w1 x ≠ u1 x := by
  by_contra hnone
  push_neg at hnone
  apply hno
  exact ⟨w0, hw0, w1, hw1, fun x hx => hnone x hx⟩

/-- At a coordinate where the fixed pencil pair differs from the received pair, at most one
scalar can make their affine combinations agree. -/
theorem scalar_eq_of_collinear_agreement_at_mismatch
    {u0 u1 w0 w1 : I -> A} {x : I} {gamma gamma' : F}
    (hgamma : w0 x + gamma • w1 x = u0 x + gamma • u1 x)
    (hgamma' : w0 x + gamma' • w1 x = u0 x + gamma' • u1 x)
    (hmismatch : w0 x ≠ u0 x ∨ w1 x ≠ u1 x) :
    gamma = gamma' := by
  by_contra hne
  have hgamma0 :
      (w0 x - u0 x) + gamma • (w1 x - u1 x) = 0 := by
    calc
      (w0 x - u0 x) + gamma • (w1 x - u1 x) =
          (w0 x + gamma • w1 x) - (u0 x + gamma • u1 x) := by module
      _ = 0 := sub_eq_zero.mpr hgamma
  have hgamma0' :
      (w0 x - u0 x) + gamma' • (w1 x - u1 x) = 0 := by
    calc
      (w0 x - u0 x) + gamma' • (w1 x - u1 x) =
          (w0 x + gamma' • w1 x) - (u0 x + gamma' • u1 x) := by module
      _ = 0 := sub_eq_zero.mpr hgamma'
  have hdirection : w1 x = u1 x := by
    have hsmul : (gamma - gamma') • (w1 x - u1 x) = 0 := by
      calc
        (gamma - gamma') • (w1 x - u1 x) =
            ((w0 x - u0 x) + gamma • (w1 x - u1 x)) -
              ((w0 x - u0 x) + gamma' • (w1 x - u1 x)) := by module
        _ = 0 := by rw [hgamma0, hgamma0', sub_zero]
    rcases smul_eq_zero.mp hsmul with hcoefficient | hvalue
    · exact (hne (sub_eq_zero.mp hcoefficient)).elim
    · exact sub_eq_zero.mp hvalue
  have hbase : w0 x = u0 x := by
    rw [hdirection] at hgamma
    exact add_right_cancel hgamma
  exact hmismatch.elim (fun h => h hbase) (fun h => h hdirection)

/-- **Collinear mismatch charge.**  Any finite scalar family admitting witnesses on one fixed
codeword pencil has cardinality at most the number of evaluation coordinates. -/
theorem card_le_domain_of_collinear_witnesses
    (C : Set (I -> A)) (u0 u1 w0 w1 : I -> A)
    (hw0 : w0 ∈ C) (hw1 : w1 ∈ C)
    (G : Finset F)
    (hwitness : ∀ gamma ∈ G, CollinearWitnessAt C u0 u1 w0 w1 gamma) :
    G.card ≤ Fintype.card I := by
  classical
  let witnessSet : {gamma // gamma ∈ G} -> Finset I := fun gamma =>
    Classical.choose (hwitness gamma gamma.property)
  have hagree : forall gamma x, x ∈ witnessSet gamma ->
      w0 x + (gamma : F) • w1 x = u0 x + (gamma : F) • u1 x := by
    intro gamma
    exact (Classical.choose_spec (hwitness gamma gamma.property)).1
  have hno : forall gamma,
      ¬ pairJointAgreesOn C (witnessSet gamma) u0 u1 := by
    intro gamma
    exact (Classical.choose_spec (hwitness gamma gamma.property)).2
  let charge : {gamma // gamma ∈ G} -> I := fun gamma =>
    Classical.choose (exists_pair_mismatch C hw0 hw1 (hno gamma))
  have hcharge : forall gamma,
      charge gamma ∈ witnessSet gamma ∧
        (w0 (charge gamma) ≠ u0 (charge gamma) ∨
          w1 (charge gamma) ≠ u1 (charge gamma)) := by
    intro gamma
    exact Classical.choose_spec (exists_pair_mismatch C hw0 hw1 (hno gamma))
  have hinjective : Function.Injective charge := by
    intro gamma gamma' heq
    apply Subtype.ext
    apply scalar_eq_of_collinear_agreement_at_mismatch
      (hagree gamma (charge gamma) (hcharge gamma).1)
    · simpa only [heq] using hagree gamma' (charge gamma') (hcharge gamma').1
    · exact (hcharge gamma).2
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective charge hinjective

end ArkLib.ProximityGap.Frontier.P1RateQuarterCollinearMismatchCharge

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCollinearMismatchCharge

#print axioms exists_pair_mismatch
#print axioms scalar_eq_of_collinear_agreement_at_mismatch
#print axioms card_le_domain_of_collinear_witnesses
