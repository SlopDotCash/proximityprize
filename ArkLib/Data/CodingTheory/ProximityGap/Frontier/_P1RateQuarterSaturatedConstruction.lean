/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorConstruction

/-!
# Saturated P1 common-factor cores and received stack

This file completes the set-theoretic heart of the saturated amplifier.  The
concrete polynomial/row substrate is supplied by
`_P1RateQuarterCommonFactorConstruction`; here we prove that

`(oldCore \ newHoles) ∪ commonRoots`

has exactly `8m+r+d` coordinates for every source line and that the amplified
polynomial pair agrees with the amplified received stack throughout it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 500000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorArithmetic
open P1RateQuarterCommonFactorConstruction
open HalfPredecessorCoreFreshDecode

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

local notation "δsat" => P1RateQuarterCommonFactorArithmetic.delta

/-! ## Membership geometry of the three modified singleton cells -/

theorem mem_core_iff_of_mem_rootFour (i : Fin 3) {e : Coord}
    (he : e ∈ rootFour) : e ∈ core i ↔ i = 0 := by
  obtain ⟨q, rfl⟩ := (mem_selectedCoords_iff (4 : Fin 16) e).1 he
  fin_cases i <;> simp [core, corePred, baseCore]

theorem mem_core_iff_of_mem_rootEleven (i : Fin 3) {e : Coord}
    (he : e ∈ rootEleven) : e ∈ core i ↔ i = 1 := by
  obtain ⟨q, rfl⟩ := (mem_selectedCoords_iff (11 : Fin 16) e).1 he
  fin_cases i <;> simp [core, corePred, baseCore]

theorem mem_core_iff_of_mem_newHoles (i : Fin 3) {e : Coord}
    (he : e ∈ newHoles) : e ∈ core i ↔ i = 2 := by
  obtain ⟨q, rfl⟩ := (mem_selectedCoords_iff (13 : Fin 16) e).1 he
  fin_cases i <;> simp [core, corePred, baseCore]

theorem newHoles_subset_core_two : newHoles ⊆ core 2 := by
  intro e he
  exact (mem_core_iff_of_mem_newHoles 2 he).2 rfl

theorem core_zero_disjoint_newHoles : Disjoint (core 0) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  exact (by decide : (0 : Fin 3) ≠ 2)
    ((mem_core_iff_of_mem_newHoles 0 hehole).1 hecore)

theorem core_one_disjoint_newHoles : Disjoint (core 1) newHoles := by
  rw [Finset.disjoint_left]
  intro e hecore hehole
  exact (by decide : (1 : Fin 3) ≠ 2)
    ((mem_core_iff_of_mem_newHoles 1 hehole).1 hecore)

theorem core_sdiff_newHoles_card (i : Fin 3) :
    (core i \ newHoles).card =
      if i = 2 then 8 * m + r - d else 8 * m + r := by
  fin_cases i
  · change (core 0 \ newHoles).card =
      if (0 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.sdiff_eq_self_of_disjoint core_zero_disjoint_newHoles,
      core_card]
    simp
  · change (core 1 \ newHoles).card =
      if (1 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.sdiff_eq_self_of_disjoint core_one_disjoint_newHoles,
      core_card]
    simp
  · change (core 2 \ newHoles).card =
      if (2 : Fin 3) = 2 then 8 * m + r - d else 8 * m + r
    rw [Finset.card_sdiff_of_subset newHoles_subset_core_two,
      core_card, newHoles_card]
    simp

theorem commonRoot_not_mem_newHoles {e : Coord} (he : e ∈ commonRoots) :
    e ∉ newHoles :=
  (Finset.disjoint_left.mp commonRoots_disjoint_newHoles) he

theorem core_zero_sdiff_inter_commonRoots :
    (core 0 \ newHoles) ∩ commonRoots = rootFour := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨hcore, -⟩, hroot⟩ := Finset.mem_inter.mp he
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact hfour
    · exact ((by decide : (0 : Fin 3) ≠ 1)
        ((mem_core_iff_of_mem_rootEleven 0 heleven).1 hcore)).elim
  · intro hfour
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨
      (mem_core_iff_of_mem_rootFour 0 hfour).2 rfl, ?_⟩, ?_⟩
    · exact commonRoot_not_mem_newHoles
        (Finset.mem_union_left rootEleven hfour)
    · exact Finset.mem_union_left rootEleven hfour

theorem core_one_sdiff_inter_commonRoots :
    (core 1 \ newHoles) ∩ commonRoots = rootEleven := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨hcore, -⟩, hroot⟩ := Finset.mem_inter.mp he
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact ((by decide : (1 : Fin 3) ≠ 0)
        ((mem_core_iff_of_mem_rootFour 1 hfour).1 hcore)).elim
    · exact heleven
  · intro heleven
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨
      (mem_core_iff_of_mem_rootEleven 1 heleven).2 rfl, ?_⟩, ?_⟩
    · exact commonRoot_not_mem_newHoles
        (Finset.mem_union_right rootFour heleven)
    · exact Finset.mem_union_right rootFour heleven

theorem core_two_sdiff_inter_commonRoots :
    (core 2 \ newHoles) ∩ commonRoots = ∅ := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨hcore, -⟩, hroot⟩ := Finset.mem_inter.mp he
    rw [commonRoots, Finset.mem_union] at hroot
    rcases hroot with hfour | heleven
    · exact ((by decide : (2 : Fin 3) ≠ 0)
        ((mem_core_iff_of_mem_rootFour 2 hfour).1 hcore)).elim
    · exact ((by decide : (2 : Fin 3) ≠ 1)
        ((mem_core_iff_of_mem_rootEleven 2 heleven).1 hcore)).elim
  · simp

theorem core_sdiff_inter_commonRoots (i : Fin 3) :
    (core i \ newHoles) ∩ commonRoots =
      if i = 0 then rootFour else if i = 1 then rootEleven else ∅ := by
  fin_cases i
  · simpa using core_zero_sdiff_inter_commonRoots
  · simpa using core_one_sdiff_inter_commonRoots
  · simpa using core_two_sdiff_inter_commonRoots

theorem core_sdiff_inter_commonRoots_card (i : Fin 3) :
    ((core i \ newHoles) ∩ commonRoots).card =
      if i = 2 then 0 else d := by
  rw [core_sdiff_inter_commonRoots]
  fin_cases i <;> simp [rootFour_card, rootEleven_card]

/-! ## Exact amplified cores -/

/-- Remove the new holes and promote all common roots into every core. -/
noncomputable def amplifiedCoreSet (i : Fin 3) : Finset Coord :=
  (core i \ newHoles) ∪ commonRoots

theorem amplifiedCoreSet_card (i : Fin 3) :
    (amplifiedCoreSet i).card = amplifiedCore := by
  have hbook := Finset.card_union_add_card_inter
    (core i \ newHoles) commonRoots
  rw [← amplifiedCoreSet, core_sdiff_newHoles_card, commonRoots_card,
    core_sdiff_inter_commonRoots_card] at hbook
  fin_cases i <;> simp at hbook <;>
    norm_num [amplifiedCore, d, m, r] at hbook ⊢ <;> omega

theorem amplifiedCoreSet_card_ge_k (i : Fin 3) :
    k ≤ (amplifiedCoreSet i).card := by
  rw [amplifiedCoreSet_card]
  norm_num [amplifiedCore, k, d, m, r]

theorem amplifiedCoreSet_size_condition (i : Fin 3) :
    ((((amplifiedCoreSet i).card + 1 : ℕ) : ℝ≥0)) ≥
      (1 - δsat) * (Fintype.card Coord : ℝ≥0) := by
  rw [amplifiedCoreSet_card, card_coord, agreement_mass_eq_amplifiedThreshold]
  rfl

/-! ## Agreement of the amplified stack on every amplified core -/

@[simp] theorem amplifiedU_zero (L : CommonLocatorData) :
    amplifiedU L 0 = amplifiedU0 L := rfl

@[simp] theorem amplifiedU_one (L : CommonLocatorData) :
    amplifiedU L 1 = amplifiedU1 L := rfl

theorem amplified_core_pair_agreement
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (he : e ∈ amplifiedCoreSet i) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU0 L e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU1 L e := by
  rw [amplifiedCoreSet, Finset.mem_union] at he
  rcases he with hold | hroot
  · have hcore : e ∈ core i := (Finset.mem_sdiff.mp hold).1
    have hnotHole : e ∉ newHoles := (Finset.mem_sdiff.mp hold).2
    have holdAgree := core_pair_agreement i e hcore
    have hrows := amplifiedU_rows_of_not_mem_newHoles L hnotHole
    rw [amplifiedIntercept_eval, amplifiedDirection_eval, hrows.1, hrows.2,
      holdAgree.1, holdAgree.2]
    constructor <;> ring
  · have hzero := L.eval_zero hroot
    have hnotHole : e ∉ newHoles := commonRoot_not_mem_newHoles hroot
    have hrows := amplifiedU_rows_of_not_mem_newHoles L hnotHole
    rw [amplifiedIntercept_eval, amplifiedDirection_eval, hrows.1, hrows.2,
      hzero]
    simp

theorem amplified_core_pair_agreement_stack
    (L : CommonLocatorData) (i : Fin 3) (e : Coord)
    (he : e ∈ amplifiedCoreSet i) :
    (amplifiedIntercept L i).eval (domain e) = amplifiedU L 0 e ∧
      (amplifiedDirection L i).eval (domain e) = amplifiedU L 1 e := by
  rw [amplifiedU_zero, amplifiedU_one]
  exact amplified_core_pair_agreement L i e he

/-! ## Safe one-fresh-coordinate certificates -/

theorem old_received_rows_on_line (e : Coord) (he : e ≠ hole) :
    u0 e = domain e * u1 e := by
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
  rcases hline : lineAt e with _ | owner
  · exact (hcovered hline).elim
  · simp only [u0, u1, hline]

noncomputable def saturatedSafeSource (e : Coord) (he : e ≠ hole) : Fin 3 :=
  P1RateQuarterScaleBadCount.safeSource e he

theorem saturatedSafeSource_not_mem_oldCore (e : Coord) (he : e ≠ hole) :
    e ∉ core (saturatedSafeSource e he) :=
  P1RateQuarterScaleBadCount.safeSource_not_mem e he

theorem saturatedSafeSource_old_mismatch (e : Coord) (he : e ≠ hole) :
    (direction (saturatedSafeSource e he)).eval (domain e) ≠ u1 e :=
  P1RateQuarterScaleBadCount.safeSource_mismatch e he

theorem saturatedSafeSource_not_mem_amplifiedCore
    (e : Coord) (he : e ≠ hole) (hroot : e ∉ commonRoots) :
    e ∉ amplifiedCoreSet (saturatedSafeSource e he) := by
  intro hmem
  rw [amplifiedCoreSet, Finset.mem_union] at hmem
  rcases hmem with hold | hcommon
  · exact saturatedSafeSource_not_mem_oldCore e he
      (Finset.mem_sdiff.mp hold).1
  · exact hroot hcommon

theorem saturated_safe_direction_mismatch
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) (hroot : e ∉ commonRoots) :
    (amplifiedDirection L (saturatedSafeSource e he)).eval (domain e) ≠
      amplifiedU1 L e := by
  rw [amplifiedDirection_eval,
    (amplifiedU_rows_of_not_mem_newHoles L hnew).2]
  intro hscaled
  apply saturatedSafeSource_old_mismatch e he
  exact mul_left_cancel₀ (L.eval_ne_zero hroot) hscaled

theorem saturated_safe_fresh_agreement
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) :
    (amplifiedIntercept L (saturatedSafeSource e he) +
      C (-domain e) * amplifiedDirection L (saturatedSafeSource e he)).eval
        (domain e) =
      amplifiedU0 L e + (-domain e) * amplifiedU1 L e := by
  let i := saturatedSafeSource e he
  have hrows := amplifiedU_rows_of_not_mem_newHoles L hnew
  have hold := old_received_rows_on_line e he
  simp only [eval_add, eval_mul, eval_C, amplifiedIntercept_eval]
  rw [hrows.1, hrows.2, hold]
  ring

theorem saturated_safe_mcaEvent
    (L : CommonLocatorData) (e : Coord) (he : e ≠ hole)
    (hnew : e ∉ newHoles) (hroot : e ∉ commonRoots) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) :
        Set (Coord → F))
      δsat (amplifiedU L 0) (amplifiedU L 1) (-domain e) := by
  let i := saturatedSafeSource e he
  apply mcaEvent_of_affine_core_fresh domain k δsat (amplifiedU L)
    (-domain e) (amplifiedCoreSet i) e
    (amplifiedIntercept L i) (amplifiedDirection L i)
  · exact saturatedSafeSource_not_mem_amplifiedCore e he hroot
  · exact amplifiedIntercept_degree_lt_k L i
  · exact amplifiedDirection_degree_lt_k L i
  · exact amplifiedAffine_degree_lt_k L i (-domain e)
  · exact amplifiedCoreSet_card_ge_k i
  · exact amplifiedCoreSet_size_condition i
  · exact amplified_core_pair_agreement_stack L i
  · have hfresh := saturated_safe_fresh_agreement L e he hnew
    simpa only [i] using hfresh
  · intro hpairs
    apply saturated_safe_direction_mismatch L e he hnew hroot
    exact congrArg Prod.snd hpairs

/-! ## The `d+1` saturated hole coordinates -/

/-- The `d` selected residue-thirteen holes followed by the old singleton
residue-fifteen hole. -/
abbrev SaturatedHoleIndex := SelectedFibreIndex ⊕ Fin 1

def saturatedHoleCoord : SaturatedHoleIndex → Coord
  | Sum.inl q => selectedCoordEmbedding 13 q
  | Sum.inr _ => hole

def saturatedHoleKind : SaturatedHoleIndex → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem saturatedHoleCoord_injective : Function.Injective saturatedHoleCoord := by
  intro a b h
  rcases a with q | a <;> rcases b with q' | b
  · apply congrArg Sum.inl
    exact (selectedCoordEmbedding 13).injective h
  · cases h
  · cases h
  · exact congrArg Sum.inr (Subsingleton.elim a b)

theorem saturatedHoleCoord_mem_newHoles (q : SelectedFibreIndex) :
    saturatedHoleCoord (Sum.inl q) ∈ newHoles := by
  exact (mem_selectedCoords_iff 13 _).2 ⟨q, rfl⟩

theorem saturatedHoleCoord_old (a : Fin 1) :
    saturatedHoleCoord (Sum.inr a) = hole := rfl

theorem saturatedHoleCoord_not_mem_commonRoots (h : SaturatedHoleIndex) :
    saturatedHoleCoord h ∉ commonRoots := by
  rcases h with q | a
  · intro hroot
    exact (Finset.disjoint_left.mp commonRoots_disjoint_newHoles) hroot
      (saturatedHoleCoord_mem_newHoles q)
  · exact hole_not_mem_commonRoots

theorem saturatedHole_locator_ne_zero (L : CommonLocatorData)
    (h : SaturatedHoleIndex) :
    L.polynomial.eval (domain (saturatedHoleCoord h)) ≠ 0 :=
  L.eval_ne_zero (saturatedHoleCoord_not_mem_commonRoots h)

theorem saturatedHoleCoord_not_mem_amplifiedCore
    (i : Fin 3) (h : SaturatedHoleIndex) :
    saturatedHoleCoord h ∉ amplifiedCoreSet i := by
  intro hmem
  rw [amplifiedCoreSet, Finset.mem_union] at hmem
  rcases hmem with hold | hroot
  · rcases h with q | a
    · exact (Finset.mem_sdiff.mp hold).2
        (saturatedHoleCoord_mem_newHoles q)
    · exact hole_not_mem_core i (Finset.mem_sdiff.mp hold).1
  · exact saturatedHoleCoord_not_mem_commonRoots h hroot

theorem saturatedHole_domain_pow_m (h : SaturatedHoleIndex) :
    domain (saturatedHoleCoord h) ^ m =
      holeFibreValue (saturatedHoleKind h) := by
  rcases h with q | a
  · rw [domain_pow_m]
    simp [saturatedHoleCoord, saturatedHoleKind, holeFibreValue,
      selectedCoordEmbedding]
  · rw [domain_pow_m]
    simp [saturatedHoleCoord, saturatedHoleKind, holeFibreValue, hole]

/-- Direction values on the two kinds of saturated holes. -/
def saturatedHoleValue : Fin 2 → Fin 3 → F := ![
  newHoleValue,
  holeValue]

theorem saturatedHoleValue_ne_two (a : Fin 2) (i : Fin 3) :
    saturatedHoleValue a i ≠ (2 : F) := by
  fin_cases a
  · exact newHoleValue_ne_two i
  · exact holeValue_ne_two i

theorem direction_eval_saturatedHole (i : Fin 3) (h : SaturatedHoleIndex) :
    (direction i).eval (domain (saturatedHoleCoord h)) =
      saturatedHoleValue (saturatedHoleKind h) i := by
  rcases h with q | a
  · exact direction_eval_newHole i (saturatedHoleCoord_mem_newHoles q)
  · simpa [saturatedHoleCoord, saturatedHoleKind, saturatedHoleValue, hole]
      using direction_eval_hole_fibre i (Sum.inr 0)

theorem saturatedHoleConstant_cross (a : Fin 2) (i : Fin 3) :
    holeConstant a i * (2 - saturatedHoleValue a i) =
      saturatedHoleValue a i - 1 := by
  fin_cases a
  · simpa [holeConstant, saturatedHoleValue] using
      (eq_div_iff (sub_ne_zero.mpr (newHoleValue_ne_two i).symm)).mp
        (newUnsafeConstant_formula i)
  · simpa [holeConstant, saturatedHoleValue] using
      (eq_div_iff (sub_ne_zero.mpr (holeValue_ne_two i).symm)).mp
        (unsafeConstant_formula i)

theorem saturatedHole_fold_identity (a : Fin 2) (i : Fin 3) :
    saturatedHoleValue a i * (1 + holeConstant a i) =
      1 + 2 * holeConstant a i := by
  have hc := saturatedHoleConstant_cross a i
  linear_combination -hc

theorem amplifiedU_rows_saturatedHole
    (L : CommonLocatorData) (h : SaturatedHoleIndex) :
    amplifiedU0 L (saturatedHoleCoord h) =
        L.polynomial.eval (domain (saturatedHoleCoord h)) *
          domain (saturatedHoleCoord h) ∧
      amplifiedU1 L (saturatedHoleCoord h) =
        L.polynomial.eval (domain (saturatedHoleCoord h)) * 2 := by
  rcases h with q | a
  · exact amplifiedU_rows_of_mem_newHoles L
      (saturatedHoleCoord_mem_newHoles q)
  · have hrows := amplifiedU_rows_of_not_mem_newHoles L
        (show hole ∉ newHoles from hole_not_mem_newHoles)
    simpa [saturatedHoleCoord, hole_rows.1, hole_rows.2] using hrows

noncomputable def saturatedUnsafeGamma
    (h : SaturatedHoleIndex) (i : Fin 3) : F :=
  holeConstant (saturatedHoleKind h) i * domain (saturatedHoleCoord h)

theorem saturated_unsafe_fresh_agreement
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    (amplifiedIntercept L i + C (saturatedUnsafeGamma h i) *
      amplifiedDirection L i).eval (domain (saturatedHoleCoord h)) =
      amplifiedU0 L (saturatedHoleCoord h) + saturatedUnsafeGamma h i *
        amplifiedU1 L (saturatedHoleCoord h) := by
  let x := domain (saturatedHoleCoord h)
  let ell := L.polynomial.eval x
  let a := saturatedHoleKind h
  let t := saturatedHoleValue a i
  let c := holeConstant a i
  have ht := direction_eval_saturatedHole i h
  have hrows := amplifiedU_rows_saturatedHole L h
  have hfold := saturatedHole_fold_identity a i
  simp only [eval_add, eval_mul, eval_C, amplifiedIntercept_eval,
    amplifiedDirection_eval]
  rw [ht, hrows.1, hrows.2]
  change x * (ell * t) + (c * x) * (ell * t) =
    ell * x + (c * x) * (ell * 2)
  calc
    x * (ell * t) + (c * x) * (ell * t) =
        ell * x * (t * (1 + c)) := by ring
    _ = ell * x * (1 + 2 * c) := by rw [hfold]
    _ = ell * x + (c * x) * (ell * 2) := by ring

theorem saturated_unsafe_pair_mismatch
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    ((amplifiedIntercept L i).eval (domain (saturatedHoleCoord h)),
      (amplifiedDirection L i).eval (domain (saturatedHoleCoord h))) ≠
      (amplifiedU0 L (saturatedHoleCoord h),
        amplifiedU1 L (saturatedHoleCoord h)) := by
  intro hpairs
  have hsecond := congrArg Prod.snd hpairs
  rw [amplifiedDirection_eval, direction_eval_saturatedHole,
    (amplifiedU_rows_saturatedHole L h).2] at hsecond
  have ht : saturatedHoleValue (saturatedHoleKind h) i = (2 : F) :=
    mul_left_cancel₀ (saturatedHole_locator_ne_zero L h) hsecond
  exact saturatedHoleValue_ne_two (saturatedHoleKind h) i ht

theorem saturated_unsafe_mcaEvent
    (L : CommonLocatorData) (h : SaturatedHoleIndex) (i : Fin 3) :
    mcaEvent
      ((ReedSolomon.code domain k : Submodule F (Coord → F)) :
        Set (Coord → F))
      δsat (amplifiedU L 0) (amplifiedU L 1)
        (saturatedUnsafeGamma h i) := by
  apply mcaEvent_of_affine_core_fresh domain k δsat (amplifiedU L)
    (saturatedUnsafeGamma h i) (amplifiedCoreSet i)
    (saturatedHoleCoord h) (amplifiedIntercept L i) (amplifiedDirection L i)
  · exact saturatedHoleCoord_not_mem_amplifiedCore i h
  · exact amplifiedIntercept_degree_lt_k L i
  · exact amplifiedDirection_degree_lt_k L i
  · exact amplifiedAffine_degree_lt_k L i (saturatedUnsafeGamma h i)
  · exact amplifiedCoreSet_card_ge_k i
  · exact amplifiedCoreSet_size_condition i
  · exact amplified_core_pair_agreement_stack L i
  · simpa only [amplifiedU_zero, amplifiedU_one] using
      saturated_unsafe_fresh_agreement L h i
  · simpa only [amplifiedU_zero, amplifiedU_one] using
      saturated_unsafe_pair_mismatch L h i

end ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterSaturatedConstruction
#print axioms amplifiedCoreSet_card
#print axioms amplified_core_pair_agreement
