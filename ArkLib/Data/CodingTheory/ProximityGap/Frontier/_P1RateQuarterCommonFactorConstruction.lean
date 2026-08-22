/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterScaleBadCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._P1RateQuarterCommonFactorArithmetic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RateQuarterCommonFactorOwnershipAmplifier
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateQuarterOverlapThreeFactorization

/-!
# Concrete P1 common-factor construction

This module realizes the saturated common-factor selector without reducing a
billion-element equivalence.  The selected fibre type is the structural sum
`Fin r ⊕ Fin (d-r)`, embedded in the first two private branches.  It has
cardinality `d=(m-2)/2` by arithmetic, so all finset cardinality proofs remain
symbolic.

Residues four and eleven supply the `2d` common roots.  Residue thirteen
supplies the `d` new holes.  The common locator amplifies each old direction,
and every amplified core is `(oldCore \ newHoles) ∪ commonRoots`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

open Finset Polynomial
open _root_.ProximityGap Code
open scoped NNReal Polynomial

namespace ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction

open ArkLib.ProximityGap.PrizeShapePrimeP30
open P1RateQuarterScaleArithmetic
open P1RateQuarterScaleConstruction
open P1RateQuarterCommonFactorArithmetic
open RateQuarterCommonFactorOwnershipAmplifier
open HalfPredecessorRateQuarterOverlapThreeFactorization

local instance localInstance_P1RateQuarterCommonFactorConstruction_1 : Fact (Nat.Prime P) := ⟨prime_P⟩
attribute [local instance] Classical.propDecidable

/-! ## Structural saturated selector -/

/-- The first full private branch and the required prefix of the second. -/
abbrev SelectedFibreIndex := Fin r ⊕ Fin (d - r)

theorem r_le_d : r ≤ d := by norm_num [r, d, m]

theorem d_sub_r_le_r : d - r ≤ r := by norm_num [r, d, m]

theorem card_selectedFibreIndex : Fintype.card SelectedFibreIndex = d := by
  norm_num [SelectedFibreIndex, r, d, m]

/-- A reduction-cheap embedding of exactly `d` quotient fibres. -/
def selectedFibreEmbedding : SelectedFibreIndex ↪ FibreIndex where
  toFun
    | Sum.inl q => Sum.inl (0, q)
    | Sum.inr q => Sum.inl (1, Fin.castLE d_sub_r_le_r q)
  inj' := by
    intro x y h
    rcases x with q | q <;> rcases y with q' | q'
    · have hp : ((0 : Fin 3), q) = ((0 : Fin 3), q') := Sum.inl.inj h
      apply congrArg Sum.inl
      exact congrArg Prod.snd hp
    · have hp : ((0 : Fin 3), q) =
          ((1 : Fin 3), Fin.castLE d_sub_r_le_r q') := Sum.inl.inj h
      exact ((by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.fst hp)).elim
    · have hp : ((1 : Fin 3), Fin.castLE d_sub_r_le_r q) =
          ((0 : Fin 3), q') := Sum.inl.inj h
      exact ((by decide : (1 : Fin 3) ≠ 0) (congrArg Prod.fst hp)).elim
    · have hp : ((1 : Fin 3), Fin.castLE d_sub_r_le_r q) =
          ((1 : Fin 3), Fin.castLE d_sub_r_le_r q') := Sum.inl.inj h
      apply congrArg Sum.inr
      exact Fin.castLE_injective d_sub_r_le_r (congrArg Prod.snd hp)

/-- Embed the selected fibres into a fixed sixteenth-root residue. -/
def selectedCoordEmbedding (a : Fin 16) : SelectedFibreIndex ↪ Coord where
  toFun q := (selectedFibreEmbedding q, a)
  inj' := by
    intro q q' h
    exact selectedFibreEmbedding.injective (congrArg Prod.fst h)

noncomputable def selectedCoords (a : Fin 16) : Finset Coord :=
  Finset.univ.map (selectedCoordEmbedding a)

theorem selectedCoords_card (a : Fin 16) : (selectedCoords a).card = d := by
  rw [selectedCoords, Finset.card_map, Finset.card_univ,
    card_selectedFibreIndex]

theorem mem_selectedCoords_iff (a : Fin 16) (e : Coord) :
    e ∈ selectedCoords a ↔
      ∃ q : SelectedFibreIndex, e = (selectedFibreEmbedding q, a) := by
  simp only [selectedCoords, Finset.mem_map, Finset.mem_univ, true_and,
    selectedCoordEmbedding]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, rfl⟩

theorem snd_eq_of_mem_selectedCoords (a : Fin 16) {e : Coord}
    (he : e ∈ selectedCoords a) : e.2 = a := by
  obtain ⟨q, rfl⟩ := (mem_selectedCoords_iff a e).1 he
  rfl

theorem selectedCoords_disjoint {a b : Fin 16} (hab : a ≠ b) :
    Disjoint (selectedCoords a) (selectedCoords b) := by
  rw [Finset.disjoint_left]
  intro e hea heb
  exact hab ((snd_eq_of_mem_selectedCoords a hea).symm.trans
    (snd_eq_of_mem_selectedCoords b heb))

noncomputable def rootFour : Finset Coord := selectedCoords 4
noncomputable def rootEleven : Finset Coord := selectedCoords 11
noncomputable def newHoles : Finset Coord := selectedCoords 13
noncomputable def commonRoots : Finset Coord := rootFour ∪ rootEleven

theorem rootFour_card : rootFour.card = d := selectedCoords_card 4
theorem rootEleven_card : rootEleven.card = d := selectedCoords_card 11
theorem newHoles_card : newHoles.card = d := selectedCoords_card 13

theorem rootFour_disjoint_rootEleven : Disjoint rootFour rootEleven :=
  selectedCoords_disjoint (by decide)

theorem commonRoots_card : commonRoots.card = 2 * d := by
  rw [commonRoots, Finset.card_union_of_disjoint rootFour_disjoint_rootEleven,
    rootFour_card, rootEleven_card]
  omega

theorem commonRoots_disjoint_newHoles : Disjoint commonRoots newHoles := by
  rw [commonRoots, Finset.disjoint_union_left]
  exact ⟨selectedCoords_disjoint (by decide),
    selectedCoords_disjoint (by decide)⟩

theorem hole_not_mem_newHoles : hole ∉ newHoles := by
  intro hmem
  have hsnd := snd_eq_of_mem_selectedCoords (13 : Fin 16) hmem
  simp [hole] at hsnd

theorem hole_not_mem_commonRoots : hole ∉ commonRoots := by
  rw [commonRoots, Finset.mem_union]
  push Not
  constructor <;> intro hmem
  · have hsnd := snd_eq_of_mem_selectedCoords (4 : Fin 16) hmem
    simp [hole] at hsnd
  · have hsnd := snd_eq_of_mem_selectedCoords (11 : Fin 16) hmem
    simp [hole] at hsnd

/-! ## Common locator and amplified lines -/

/-- The locator interface used downstream: a degree bound, vanishing on the
selected roots, and nonvanishing everywhere else in the evaluation domain. -/
structure CommonLocatorData where
  polynomial : F[X]
  natDegree_le : polynomial.natDegree ≤ 2 * d
  eval_zero : ∀ {e : Coord}, e ∈ commonRoots → polynomial.eval (domain e) = 0
  eval_ne_zero : ∀ {e : Coord}, e ∉ commonRoots → polynomial.eval (domain e) ≠ 0

/-- Existence proposition for a package satisfying the locator interface.
`commonLocatorResidual` below discharges it unconditionally. -/
def CommonLocatorResidual : Prop := Nonempty CommonLocatorData

theorem eval_domainRootProduct_eq_zero_iff_mem
    {I : Type} [Fintype I] [DecidableEq I]
    (dom : I ↪ F) (S : Finset I) (i : I) :
    (domainRootProduct dom S).eval (dom i) = 0 ↔ i ∈ S := by
  rw [domainRootProduct, eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, hj, hzero⟩
    simp only [eval_sub, eval_X, eval_C] at hzero
    exact dom.injective (sub_eq_zero.mp hzero) ▸ hj
  · intro hi
    exact ⟨i, hi, by simp⟩

noncomputable def concreteCommonLocatorPolynomial : F[X] :=
  domainRootProduct domain commonRoots

theorem concreteCommonLocator_natDegree :
    concreteCommonLocatorPolynomial.natDegree = 2 * d := by
  rw [concreteCommonLocatorPolynomial, domainRootProduct_natDegree,
    commonRoots_card]

theorem concreteCommonLocator_eval_zero {e : Coord} (he : e ∈ commonRoots) :
    concreteCommonLocatorPolynomial.eval (domain e) = 0 := by
  exact (eval_domainRootProduct_eq_zero_iff_mem domain commonRoots e).2 he

theorem concreteCommonLocator_eval_ne_zero {e : Coord} (he : e ∉ commonRoots) :
    concreteCommonLocatorPolynomial.eval (domain e) ≠ 0 := by
  exact (eval_domainRootProduct_eq_zero_iff_mem domain commonRoots e).not.mpr he

theorem commonLocatorResidual : CommonLocatorResidual := by
  exact ⟨⟨concreteCommonLocatorPolynomial,
    concreteCommonLocator_natDegree.le,
    fun he ↦ concreteCommonLocator_eval_zero he,
    fun he ↦ concreteCommonLocator_eval_ne_zero he⟩⟩

noncomputable def commonLocatorData : CommonLocatorData :=
  Classical.choice commonLocatorResidual

noncomputable def amplifiedDirection (L : CommonLocatorData) (i : Fin 3) : F[X] :=
  amplifiedFactor L.polynomial (direction i)

noncomputable def amplifiedIntercept (L : CommonLocatorData) (i : Fin 3) : F[X] :=
  (Polynomial.X : F[X]) * amplifiedDirection L i

theorem amplifiedDirection_eval (L : CommonLocatorData) (i : Fin 3) (e : Coord) :
    (amplifiedDirection L i).eval (domain e) =
      L.polynomial.eval (domain e) * (direction i).eval (domain e) := by
  simp only [amplifiedDirection, amplifiedFactor, eval_mul]

theorem amplifiedIntercept_eval (L : CommonLocatorData) (i : Fin 3) (e : Coord) :
    (amplifiedIntercept L i).eval (domain e) =
      domain e * (amplifiedDirection L i).eval (domain e) := by
  simp only [amplifiedIntercept, eval_mul, eval_X]

theorem amplified_natDegree_bounds (L : CommonLocatorData) (i : Fin 3) :
    (amplifiedDirection L i).natDegree ≤ 3 * m + 2 * d ∧
      (amplifiedIntercept L i).natDegree ≤ 3 * m + 2 * d + 1 := by
  have h := amplified_polynomial_natDegree_bounds L.polynomial (direction i)
    L.natDegree_le (direction_natDegree_le i)
  simpa only [amplifiedDirection, amplifiedIntercept, amplifiedLine] using
    And.intro h.1 h.2.1

theorem amplifiedDirection_degree_lt_k (L : CommonLocatorData) (i : Fin 3) :
    (amplifiedDirection L i).degree < (k : ℕ) := by
  apply degree_lt_of_natDegree_lt_k
  exact (amplified_natDegree_bounds L i).1.trans_lt
    (by
      have h := common_factor_degree_budget.2
      omega)

theorem amplifiedIntercept_degree_lt_k (L : CommonLocatorData) (i : Fin 3) :
    (amplifiedIntercept L i).degree < (k : ℕ) := by
  apply degree_lt_of_natDegree_lt_k
  exact (amplified_natDegree_bounds L i).2.trans_lt
    common_factor_degree_budget.2

theorem amplifiedAffine_degree_lt_k
    (L : CommonLocatorData) (i : Fin 3) (gamma : F) :
    (amplifiedIntercept L i + C gamma * amplifiedDirection L i).degree < (k : ℕ) := by
  apply degree_lt_of_natDegree_lt_k
  refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact (amplified_natDegree_bounds L i).2.trans_lt
      common_factor_degree_budget.2
  · exact (natDegree_C_mul_le gamma (amplifiedDirection L i)).trans_lt
      ((amplified_natDegree_bounds L i).1.trans_lt
        (by
          have h := common_factor_degree_budget.2
          omega))

/-! ## Scaled received rows -/

noncomputable def amplifiedU1 (L : CommonLocatorData) (e : Coord) : F :=
  if e ∈ newHoles then L.polynomial.eval (domain e) * 2
  else L.polynomial.eval (domain e) * u1 e

noncomputable def amplifiedU0 (L : CommonLocatorData) (e : Coord) : F :=
  if e ∈ newHoles then L.polynomial.eval (domain e) * domain e
  else L.polynomial.eval (domain e) * u0 e

noncomputable def amplifiedU (L : CommonLocatorData) : WordStack F (Fin 2) Coord :=
  fun row => Fin.cases (amplifiedU0 L) (fun _ => amplifiedU1 L) row

theorem amplifiedU_rows_of_not_mem_newHoles
    (L : CommonLocatorData) {e : Coord} (he : e ∉ newHoles) :
    amplifiedU0 L e = L.polynomial.eval (domain e) * u0 e ∧
      amplifiedU1 L e = L.polynomial.eval (domain e) * u1 e := by
  simp only [amplifiedU0, amplifiedU1, if_neg he, and_self]

theorem amplifiedU_rows_of_mem_newHoles
    (L : CommonLocatorData) {e : Coord} (he : e ∈ newHoles) :
    amplifiedU0 L e = L.polynomial.eval (domain e) * domain e ∧
      amplifiedU1 L e = L.polynomial.eval (domain e) * 2 := by
  simp only [amplifiedU0, amplifiedU1, if_pos he, and_self]

theorem baseValue_thirteen (i : Fin 3) :
    baseValue i 13 = newHoleValue i := by
  fin_cases i <;>
    simp [baseValue, locatorAValue, locatorCValue, newHoleValue,
      lambdaValue, z] <;> decide

theorem direction_eval_newHole (i : Fin 3) {e : Coord} (he : e ∈ newHoles) :
    (direction i).eval (domain e) = newHoleValue i := by
  rw [direction_eval, snd_eq_of_mem_selectedCoords (13 : Fin 16) he,
    baseValue_thirteen]

end ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction

/-! ## Axiom audit -/

open ArkLib.ProximityGap.Frontier.P1RateQuarterCommonFactorConstruction
#print axioms selectedCoords_card
#print axioms commonRoots_card
#print axioms concreteCommonLocator_natDegree
#print axioms concreteCommonLocator_eval_zero
#print axioms concreteCommonLocator_eval_ne_zero
#print axioms commonLocatorResidual
#print axioms commonLocatorData
#print axioms amplifiedAffine_degree_lt_k
#print axioms direction_eval_newHole
