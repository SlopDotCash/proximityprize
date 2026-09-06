/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernelUD

/-!
# A reusable core-plus-one-fresh-coordinate MCA certificate

This file isolates the algebraic mechanism used by the smooth rate-quarter
construction.  A core of at least `k` coordinates uniquely fixes each row of a
degree-`<k` polynomial pair.  Hence a single fresh-coordinate mismatch rules
out joint agreement, while the affine specialization may still decode the
fold on the enlarged support.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F]

/-- A core of at least `k` evaluation points uniquely determines both
degree-`<k` rows.  A mismatch at one inserted point therefore forbids a joint
Reed--Solomon explanation on the enlarged support. -/
theorem not_pairJointAgreesOn_insert_core
    (domain : I ↪ F) (k : ℕ) (u : WordStack F (Fin 2) I)
    (D : Finset I) (e : I) (a r : F[X])
    (ha : a.degree < (k : ℕ)) (hr : r.degree < (k : ℕ))
    (hcard : k ≤ D.card)
    (hcore : ∀ i ∈ D,
      a.eval (domain i) = u 0 i ∧ r.eval (domain i) = u 1 i)
    (hmismatch :
      (a.eval (domain e), r.eval (domain e)) ≠ (u 0 e, u 1 e)) :
    ¬ pairJointAgreesOn
      ((ReedSolomon.code domain k : Submodule F (I → F)) : Set (I → F))
      (insert e D) (u 0) (u 1) := by
  rintro ⟨v0, hv0, v1, hv1, hagree⟩
  change v0 ∈ ReedSolomon.code domain k at hv0
  change v1 ∈ ReedSolomon.code domain k at hv1
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv0 hv1
  obtain ⟨p0, hp0, hv0⟩ := hv0
  obtain ⟨p1, hp1, hv1⟩ := hv1
  have hp0eq : p0 = a := by
    apply sub_eq_zero.mp
    apply eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp0 ha))
      D hcard
    intro i hi
    have hreceived := (hagree i (Finset.mem_insert_of_mem hi)).1
    have hpoly : p0.eval (domain i) = u 0 i := by
      rw [hv0] at hreceived
      simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply] using hreceived
    rw [eval_sub, hpoly, (hcore i hi).1, sub_self]
  have hp1eq : p1 = r := by
    apply sub_eq_zero.mp
    apply eq_zero_of_degree_lt_of_vanishes_on
      (lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp1 hr))
      D hcard
    intro i hi
    have hreceived := (hagree i (Finset.mem_insert_of_mem hi)).2
    have hpoly : p1.eval (domain i) = u 1 i := by
      rw [hv1] at hreceived
      simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply] using hreceived
    rw [eval_sub, hpoly, (hcore i hi).2, sub_self]
  apply hmismatch
  have hfresh := hagree e (Finset.mem_insert_self e D)
  have hfirst : a.eval (domain e) = u 0 e := by
    have h := hfresh.1
    rw [hv0, hp0eq] at h
    simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply] using h
  have hsecond : r.eval (domain e) = u 1 e := by
    have h := hfresh.2
    rw [hv1, hp1eq] at h
    simpa only [ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply] using h
  exact Prod.ext hfirst hsecond

/-- Package the core-plus-fresh mechanism directly as a literal `McaDecode`.
The size inequality is stated with `D.card + 1`, so it can be reused at any
radius whose agreement threshold is met by the enlarged support. -/
noncomputable def decodeOfAffineCoreFresh
    (domain : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u : WordStack F (Fin 2) I)
    (γ : F) (D : Finset I) (e : I) (a r : F[X])
    (he : e ∉ D)
    (ha : a.degree < (k : ℕ)) (hr : r.degree < (k : ℕ))
    (hq : (a + C γ * r).degree < (k : ℕ))
    (hcoreCard : k ≤ D.card)
    (hsize : ((D.card + 1 : ℕ) : ℝ≥0) ≥
      (1 - δ) * (Fintype.card I : ℝ≥0))
    (hcore : ∀ i ∈ D,
      a.eval (domain i) = u 0 i ∧ r.eval (domain i) = u 1 i)
    (hfresh : (a + C γ * r).eval (domain e) =
      u 0 e + γ * u 1 e)
    (hmismatch :
      (a.eval (domain e), r.eval (domain e)) ≠ (u 0 e, u 1 e)) :
    McaDecode domain k δ u γ where
  S := insert e D
  P := a + C γ * r
  hdeg := hq
  hcard := by simpa [Finset.card_insert_of_notMem he] using hsize
  hagree := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · simpa only [smul_eq_mul] using hfresh
    · obtain ⟨haEval, hrEval⟩ := hcore i hi
      simp only [eval_add, eval_mul, eval_C, smul_eq_mul]
      rw [haEval, hrEval]
  hnjp := not_pairJointAgreesOn_insert_core domain k u D e a r ha hr
    hcoreCard hcore hmismatch

/-- The corresponding literal bad-scalar event. -/
theorem mcaEvent_of_affine_core_fresh
    (domain : I ↪ F) (k : ℕ) (δ : ℝ≥0) (u : WordStack F (Fin 2) I)
    (γ : F) (D : Finset I) (e : I) (a r : F[X])
    (he : e ∉ D)
    (ha : a.degree < (k : ℕ)) (hr : r.degree < (k : ℕ))
    (hq : (a + C γ * r).degree < (k : ℕ))
    (hcoreCard : k ≤ D.card)
    (hsize : ((D.card + 1 : ℕ) : ℝ≥0) ≥
      (1 - δ) * (Fintype.card I : ℝ≥0))
    (hcore : ∀ i ∈ D,
      a.eval (domain i) = u 0 i ∧ r.eval (domain i) = u 1 i)
    (hfresh : (a + C γ * r).eval (domain e) =
      u 0 e + γ * u 1 e)
    (hmismatch :
      (a.eval (domain e), r.eval (domain e)) ≠ (u 0 e, u 1 e)) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (I → F)) : Set (I → F))
      δ (u 0) (u 1) γ :=
  (decodeOfAffineCoreFresh domain k δ u γ D e a r he ha hr hq
    hcoreCard hsize hcore hfresh hmismatch).mcaEvent

end ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.HalfPredecessorCoreFreshDecode
#print axioms not_pairJointAgreesOn_insert_core
#print axioms mcaEvent_of_affine_core_fresh
