/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleConstruction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleOperationalCountConnector
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation

/-!
# The prize-scale rate-quarter bad-scalar certificate

This file completes the operational assembly of the maximally thickened
three-line construction over the first certified prize prime.  Every non-hole
coordinate gives the safe scalar `-x`; the singleton hole gives three further
scalars.  The resulting `N+2` distinct bad scalars exceed the exact `N` budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 500000
set_option maxRecDepth 500000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal ENNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterScaleBadCount

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterScaleOperationalCountConnector
open HalfPredecessorCoreFreshDecode

local instance localInstance_P1RateQuarterScaleBadCount_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

/-- A source line which misses each ordinary quotient residue and has a
different direction value from the line storing the received row there. -/
def sourceResidue : Fin 16 → Fin 3 := ![
  2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 1]

theorem sourceResidue_not_mem (a : Fin 16) (ha : a ≠ 15) :
    a ∉ baseCore (sourceResidue a) := by
  fin_cases a <;> decide

theorem sourceResidue_value_ne (a : Fin 16) (ha : a ≠ 15) :
    baseValue (sourceResidue a) a ≠ baseValue (ordinaryLine a) a := by
  fin_cases a <;>
    simp [sourceResidue, ordinaryLine, baseValue, locatorAValue, locatorCValue] <;>
    decide

/-- Every covered coordinate has a decoded source line which does not own it
and whose direction row genuinely mismatches the received row there. -/
theorem exists_safe_source (e : Coord) (he : e ≠ hole) :
    ∃ i : Fin 3, e ∉ core i ∧ (direction i).eval (domain e) ≠ u1 e := by
  rcases e with ⟨j, a⟩
  by_cases ha : a = (15 : Fin 16)
  · subst a
    rcases j with ⟨owner, q⟩ | hlast
    · fin_cases owner
      · refine ⟨1, ?_, ?_⟩
        · simp [core, corePred, baseCore]
        · rw [direction_eval_hole_fibre]
          simp only [u1, lineAt_transfer]
          rw [direction_eval_hole_fibre]
          intro h
          exact (by decide : (1 : Fin 3) ≠ 0) (holeValue_pairwise_ne h)
      · refine ⟨2, ?_, ?_⟩
        · simp [core, corePred, baseCore]
        · rw [direction_eval_hole_fibre]
          simp only [u1, lineAt_transfer]
          rw [direction_eval_hole_fibre]
          intro h
          exact (by decide : (2 : Fin 3) ≠ 1) (holeValue_pairwise_ne h)
      · refine ⟨0, ?_, ?_⟩
        · simp [core, corePred, baseCore]
        · rw [direction_eval_hole_fibre]
          simp only [u1, lineAt_transfer]
          rw [direction_eval_hole_fibre]
          intro h
          exact (by decide : (0 : Fin 3) ≠ 2) (holeValue_pairwise_ne h)
    · exfalso
      apply he
      apply Prod.ext
      · exact congrArg Sum.inr (Subsingleton.elim hlast 0)
      · rfl
  · have hline : lineAt (j, a) = some (ordinaryLine a) := by
      simp [lineAt, ha]
    refine ⟨sourceResidue a, ?_, ?_⟩
    · simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, corePred]
      intro hmem
      rcases hmem with hbase | htransfer
      · exact sourceResidue_not_mem a ha hbase
      · exact ha htransfer.2
    · simp only [u1, hline]
      rw [direction_eval, direction_eval]
      exact sourceResidue_value_ne a ha

/-- A covered coordinate's safe scalar. -/
noncomputable def safeGamma (e : Coord) : F := -domain e

/-- The source line selected by `exists_safe_source`. -/
noncomputable def safeSource (e : Coord) (he : e ≠ hole) : Fin 3 :=
  Classical.choose (exists_safe_source e he)

theorem safeSource_not_mem (e : Coord) (he : e ≠ hole) :
    e ∉ core (safeSource e he) :=
  (Classical.choose_spec (exists_safe_source e he)).1

theorem safeSource_mismatch (e : Coord) (he : e ≠ hole) :
    (direction (safeSource e he)).eval (domain e) ≠ u1 e :=
  (Classical.choose_spec (exists_safe_source e he)).2

/-- Every non-hole coordinate supplies a literal bad scalar at the thickened radius. -/
theorem safe_mcaEvent (e : Coord) (he : e ≠ hole) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) (safeGamma e) := by
  let i := safeSource e he
  apply mcaEvent_of_affine_core_fresh domain k delta u (safeGamma e)
    (core i) e (intercept i) (direction i)
  · exact safeSource_not_mem e he
  · exact intercept_degree_lt_k i
  · exact direction_degree_lt_k i
  · exact affine_degree_lt_k i (safeGamma e)
  · rw [core_card]
    norm_num [k, m, r]
  · rw [core_card, card_coord, agreement_mass_eq_threshold]
  · exact core_pair_agreement i
  · simp only [safeGamma, intercept, eval_add, eval_mul, eval_C, eval_X,
      u_zero, u_one, smul_eq_mul]
    have hcovered : lineAt e ≠ none := by
      intro hnone
      rcases e with ⟨j, a⟩
      simp only [lineAt] at hnone
      split at hnone
      · rename_i ha
        subst a
        rcases j with iq | hlast
        · simp at hnone
        · apply he
          exact Prod.ext (congrArg Sum.inr (Subsingleton.elim hlast 0)) rfl
      · simp at hnone
    rcases hline : lineAt e with j | owner
    · exact (hcovered hline).elim
    · simp only [u0, u1, hline]
      ring
  · intro hpairs
    apply safeSource_mismatch e he
    exact congrArg Prod.snd hpairs

/-- Safe labels are injective because the smooth evaluation domain is. -/
theorem safeGamma_injective : Function.Injective safeGamma := by
  intro e e' h
  apply domain.injective
  exact neg_injective h

/-- The three affine-hole labels. -/
noncomputable def unsafeGamma (i : Fin 3) : F :=
  unsafeConstant i * domain hole

theorem hole_fold_identity (i : Fin 3) :
    holeValue i * (1 + unsafeConstant i) = 1 + 2 * unsafeConstant i := by
  have hc := unsafeConstant_formula i
  have hden : (2 : F) - holeValue i ≠ 0 :=
    sub_ne_zero.mpr (holeValue_ne_two i).symm
  have hc' := (eq_div_iff hden).mp hc
  linear_combination -hc'

/-- Each exact hole multiplier gives a third, unsafe bad scalar. -/
theorem unsafe_mcaEvent (i : Fin 3) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) (unsafeGamma i) := by
  apply mcaEvent_of_affine_core_fresh domain k delta u (unsafeGamma i)
    (core i) hole (intercept i) (direction i)
  · exact hole_not_mem_core i
  · exact intercept_degree_lt_k i
  · exact direction_degree_lt_k i
  · exact affine_degree_lt_k i (unsafeGamma i)
  · rw [core_card]
    norm_num [k, m, r]
  · rw [core_card, card_coord, agreement_mass_eq_threshold]
  · exact core_pair_agreement i
  · rw [eval_add, eval_mul, eval_C, intercept, eval_mul, eval_X]
    have ht : (direction i).eval (domain hole) = holeValue i := by
      simpa only [hole] using direction_eval_hole_fibre i (Sum.inr 0)
    rw [ht]
    have hx0 := domain_ne_zero hole
    rw [u_zero, u_one, hole_rows.1, hole_rows.2, unsafeGamma]
    calc
      domain hole * holeValue i + unsafeConstant i * domain hole * holeValue i =
          domain hole * (holeValue i * (1 + unsafeConstant i)) := by ring
      _ = domain hole * (1 + 2 * unsafeConstant i) := by rw [hole_fold_identity]
      _ = domain hole + unsafeConstant i * domain hole * 2 := by ring
  · intro hpairs
    have hsecond := congrArg Prod.snd hpairs
    simp only at hsecond
    have ht : (direction i).eval (domain hole) = holeValue i := by
      simpa only [hole] using direction_eval_hole_fibre i (Sum.inr 0)
    rw [ht, u_one, hole_rows.2] at hsecond
    exact holeValue_ne_two i hsecond

theorem domain_pow_N_eq_one (e : Coord) : domain e ^ N = (1 : F) := by
  rw [domain_apply, ← pow_mul]
  have hdiv : N ∣ ((e.2 : ℕ) + 16 * fibreNat e.1) * N := dvd_mul_left _ _
  obtain ⟨s, hs⟩ := hdiv
  rw [hs, pow_mul, g_pow_N, one_pow]

theorem safeGamma_pow_N_eq_one (e : Coord) : safeGamma e ^ N = (1 : F) := by
  rw [safeGamma, neg_pow, domain_pow_N_eq_one]
  norm_num [N]

theorem unsafeGamma_pow_N_ne_one (i : Fin 3) :
    unsafeGamma i ^ N ≠ (1 : F) := by
  rw [unsafeGamma, mul_pow, domain_pow_N_eq_one, mul_one]
  exact unsafeConstant_pow_N_ne_one i

theorem unsafeGamma_injective : Function.Injective unsafeGamma := by
  intro i j hij
  have hx0 := domain_ne_zero hole
  apply unsafeConstant_injective
  exact mul_right_cancel₀ hx0 hij

theorem unsafeGamma_ne_safeGamma (i : Fin 3) (e : Coord) :
    unsafeGamma i ≠ safeGamma e := by
  intro h
  apply unsafeGamma_pow_N_ne_one i
  rw [h, safeGamma_pow_N_eq_one]

/-- The `N-1` covered coordinates in a structural, non-enumerating presentation. -/
abbrev SafeCoord := ((Fin 3 × Fin r) × Fin 16) ⊕ Fin 15

def safeCoordToCoord : SafeCoord → Coord
  | Sum.inl e => (Sum.inl e.1, e.2)
  | Sum.inr a => (Sum.inr 0, ⟨a, by omega⟩)

theorem safeCoordToCoord_injective : Function.Injective safeCoordToCoord := by
  intro x y h
  rcases x with e | a <;> rcases y with e' | b
  · apply congrArg Sum.inl
    change (Sum.inl e.1, e.2) = (Sum.inl e'.1, e'.2) at h
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h))
      (congrArg (fun z : Coord => z.2) h)
  · cases h
  · cases h
  · apply congrArg Sum.inr
    apply Fin.ext
    exact congrArg (fun e : Coord => (e.2 : ℕ)) h

noncomputable def scalarLabel : SafeCoord ⊕ Fin 3 → F
  | Sum.inl e => safeGamma (safeCoordToCoord e)
  | Sum.inr i => unsafeGamma i

theorem scalarLabel_injective : Function.Injective scalarLabel := by
  intro x y h
  rcases x with e | i <;> rcases y with e' | j
  · congr 1
    exact safeCoordToCoord_injective (safeGamma_injective h)
  · exact (unsafeGamma_ne_safeGamma j (safeCoordToCoord e) h.symm).elim
  · exact (unsafeGamma_ne_safeGamma i (safeCoordToCoord e') h).elim
  · congr 1
    exact unsafeGamma_injective h

theorem safeCoord_ne_hole (e : SafeCoord) : safeCoordToCoord e ≠ hole := by
  rcases e with e | a
  · intro h
    cases h
  · intro h
    have := congrArg (fun e : Coord => (e.2 : ℕ)) h
    simp [safeCoordToCoord, hole] at this
    omega

theorem scalarLabel_mcaEvent (x : SafeCoord ⊕ Fin 3) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) (scalarLabel x) := by
  rcases x with e | i
  · exact safe_mcaEvent (safeCoordToCoord e) (safeCoord_ne_hole e)
  · exact unsafe_mcaEvent i

noncomputable def scalarLabelEmbedding : SafeCoord ⊕ Fin 3 ↪ F :=
  ⟨scalarLabel, scalarLabel_injective⟩

noncomputable def badScalars : Finset F :=
  Finset.univ.map scalarLabelEmbedding

theorem badScalars_card : badScalars.card = N + 2 := by
  rw [badScalars, Finset.card_map, Finset.card_univ, Fintype.card_sum]
  norm_num [r, N]

theorem badScalars_mcaEvent (γ : F) (hγ : γ ∈ badScalars) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      delta (u 0) (u 1) γ := by
  rw [badScalars, Finset.mem_map] at hγ
  obtain ⟨x, -, rfl⟩ := hγ
  exact scalarLabel_mcaEvent x

/-- The explicit stack has at least `N+2` distinct bad scalars. -/
theorem badScalar_filter_card_ge_N_add_two :
    N + 2 ≤ (Finset.univ.filter fun γ : F =>
      mcaEvent
        ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
        delta (u 0) (u 1) γ).card := by
  rw [← badScalars_card]
  apply Finset.card_le_card
  intro γ hγ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [badScalars, Finset.mem_map] at hγ
  obtain ⟨x, -, rfl⟩ := hγ
  exact scalarLabel_mcaEvent x

/-- The `N+2` bad labels cost strictly more than the target `2^-128`. -/
theorem inverse_two_pow_128_lt_badScalars_price :
    (((2 ^ 128 : ℕ) : ENNReal)⁻¹ : ENNReal) <
      (badScalars.card : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [badScalars_card, ZMod.card]
  exact prizeEpsilon_lt_N_add_two_div_P

/-- **Prize-scale rate-quarter upper bound.**  The first-prime operational
threshold is at most `23/48 - 2/(3N)`, strictly below one half. -/
theorem firstPrime_rateQuarter_mcaDeltaStar_le_delta :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar
      (F := F) (A := F)
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
      (((2 ^ 128 : ℕ) : ENNReal)⁻¹ : ENNReal) ≤ delta := by
  exact ProximityGap.MCAListBracketInterpolation.mcaDeltaStar_le_of_badStack
    ((ReedSolomon.code domain k : Submodule F (Coord → F)) : Set (Coord → F))
    u badScalars badScalars_mcaEvent inverse_two_pow_128_lt_badScalars_price

#print axioms exists_safe_source
#print axioms safe_mcaEvent
#print axioms safeGamma_injective
#print axioms unsafe_mcaEvent
#print axioms badScalar_filter_card_ge_N_add_two
#print axioms firstPrime_rateQuarter_mcaDeltaStar_le_delta

end ArkLib.ProximityGap.Frontier.P1RateQuarterScaleBadCount
