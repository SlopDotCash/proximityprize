/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.RateHalfSevenTwentyFourths
import ArkLib.Research.ProximityGap.Frontier.FourHeadWitness
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Four large joint agreement cores on the first production domain

The coordinates are the actual powers of the first prime's generator. Grouping them by their
index modulo sixteen reduces cardinality computations to two intervals per fiber. -/

namespace ProximityGap.FirstPrimeSepticCores

open ArkLib.ProximityGap.PrizeShapePrimeP30 (orderOf_g)
private abbrev generator := ArkLib.ProximityGap.PrizeShapePrimeP30.g
open RateHalfSevenTwentyFourths (classID omega head equality_class_table)
open Finset Polynomial
open scoped BigOperators NNReal ENNReal

set_option autoImplicit false
set_option maxRecDepth 8192

abbrev N := 1073741824
abbrev S := 67108864
abbrev F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P
local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

/-- The evaluation domain in the original order of the generator powers. -/
def domain : Fin N ↪ F :=
  KKH26RegimeSplit.powDomain generator orderOf_g (KKH26RegimeSplit.ne_zero_of_orderOf_eq orderOf_g)

private abbrev Grid := Σ _ : Fin 16, Fin S
private noncomputable def index : Grid ≃ Fin N :=
  (Equiv.sigmaEquivProd _ _).trans ((Equiv.prodComm _ _).trans finProdFinEquiv)

private def cut (j : Fin 16) : ℕ :=
  if j = 3 then 11184809 else if j = 7 then 44739243 else
  if j = 11 then 11184810 else if j = 15 then 33554432 else S

private theorem cut_le : ∀ j, cut j ≤ S := by decide

private inductive Slot where
  | root
  | off
  | ordinary (representative : Fin 4)
  deriving DecidableEq

private def slot (j : Fin 16) (second : Bool) : Slot :=
  if j = 3 then (if second then .ordinary 1 else .root)
  else if j = 7 then (if second then .off else .root)
  else if j = 11 then (if second then .ordinary 0 else .root)
  else if j = 15 then (if second then .ordinary 1 else .ordinary 0)
  else .ordinary (![1,1,0,0,0,0,0,0,1,0,0,0,0,0,0,0] j)

private noncomputable def lower (j : Fin 16) : Finset (Fin S) :=
  univ.filter (fun r => r.val < cut j)

private theorem card_lower (j : Fin 16) : (lower j).card = cut j := by
  rw [lower, Fin.card_filter_val_lt, Nat.min_eq_right (cut_le j)]

private abbrev Selection := Fin 16 → Bool → Bool

private noncomputable def row (take : Selection) (j : Fin 16) : Finset (Fin S) :=
  (if take j false then lower j else ∅) ∪ (if take j true then (lower j)ᶜ else ∅)

private noncomputable def selected (take : Selection) : Finset (Fin N) :=
  (univ.sigma (row take)).map index.toEmbedding

private theorem card_selected (take : Selection) :
    (selected take).card = ∑ j : Fin 16,
      ((if take j false then cut j else 0) + (if take j true then S - cut j else 0)) := by
  rw [selected, card_map, card_sigma]
  apply sum_congr rfl
  intro j _
  cases h1 : take j false <;> cases h2 : take j true <;>
    simp [row, h1, h2, card_lower, card_compl, Nat.add_sub_of_le (cut_le j)]

private theorem mem_selected (take : Selection) (u : Grid) :
    index u ∈ selected take ↔ take u.1 (decide (cut u.1 ≤ u.2.val)) := by
  classical
  change index.toEmbedding u ∈ (univ.sigma (row take)).map index.toEmbedding ↔ _
  rw [mem_map_equiv]
  simp only [mem_sigma, mem_univ, true_and]
  by_cases h : u.2.val < cut u.1
  · have h' := Nat.not_le.mpr h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]
  · have h' := Nat.le_of_not_gt h
    cases h1 : take u.1 false <;> cases h2 : take u.1 true <;> simp [row, h, h', lower, h1, h2]

private def rootSel : Selection := fun j b => decide (slot j b = .root)
private def offSel : Selection := fun j b => decide (slot j b = .off)
private def ordinarySel : Selection := fun j b => match slot j b with
  | .ordinary _ => true
  | _ => false
private def coreSel (i : Fin 4) : Selection := fun j b => match slot j b with
  | .root => true
  | .off => false
  | .ordinary h => decide (classID j i = classID j h)

noncomputable def roots : Finset (Fin N) := selected rootSel
noncomputable def ordinary : Finset (Fin N) := selected ordinarySel
noncomputable def special : Finset (Fin N) := selected offSel
noncomputable def core (i : Fin 4) : Finset (Fin N) := selected (coreSel i)

/-- All counts use the actual finite subsets, including the split fiber at index fifteen. -/
theorem population : roots.card = S - 2 ∧ ordinary.card + 4 * special.card = N + 1 ∧
    ∀ i : Fin 4, (core i).card = ![760567124,760567125,760567124,760567125] i := by
  simp only [roots, ordinary, special, core, card_selected]
  decide

attribute [irreducible] roots ordinary special core

private noncomputable def quotient (i : Fin 4) : F[X] :=
  let a : F := omega ^ (4 * i.val)
  (Polynomial.X ^ 6 + C a * Polynomial.X ^ 4 + C (a ^ 2) * Polynomial.X ^ 2 + C (a ^ 3)) *
    (C (a + omega ^ 2 * a ^ 2) * Polynomial.X + C (omega ^ 5 + omega ^ 3 * a ^ 3))

private theorem quotient_eval (i : Fin 4) (y : F) :
    (quotient i).eval y = head omega i y := by simp [quotient, head, add_assoc]

private theorem septic_degree {K : Type} [Field K] (a b c : K) :
    (((Polynomial.X : K[X]) ^ 6 + C a * Polynomial.X ^ 4 +
      C (a ^ 2) * Polynomial.X ^ 2 + C (a ^ 3)) *
      (C b * Polynomial.X + C c)).natDegree ≤ 7 := by
  have h₁ : ((Polynomial.X : K[X]) ^ 6 + C a * Polynomial.X ^ 4 +
      C (a ^ 2) * Polynomial.X ^ 2 + C (a ^ 3)).natDegree ≤ 6 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (by simp only [natDegree_X_pow, le_refl])
          ((natDegree_C_mul_X_pow_le a 4).trans (by decide)))
        ((natDegree_C_mul_X_pow_le (a ^ 2) 2).trans (by decide)))
      (by simp only [natDegree_C, Nat.zero_le])
  have h₂ : (C b * Polynomial.X + C c).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le ((natDegree_C_mul_le b Polynomial.X).trans natDegree_X_le)
      (by simp only [natDegree_C, Nat.zero_le])
  exact natDegree_mul_le.trans (Nat.add_le_add h₁ h₂)

private theorem quotient_degree (i : Fin 4) : (quotient i).natDegree ≤ 7 := by
  unfold quotient
  exact septic_degree _ _ _

private theorem domain_power (u : Grid) : (domain (index u)) ^ S = omega ^ u.1.val := by
  change (generator ^ (u.1.val + 16 * u.2.val)) ^ S = _
  have horder : orderOf generator = N := orderOf_g
  have hg : generator ^ N = 1 := horder ▸ pow_orderOf_eq_one generator
  have hr : (generator ^ (16 * u.2.val)) ^ S = 1 := by
    have h : 16 * u.2.val * S = N * u.2.val := by
      change 16 * u.2.val * 67108864 = (16 * 67108864) * u.2.val
      ac_rfl
    rw [← pow_mul, h, pow_mul, hg, one_pow]
  have hroot : generator ^ S = omega := rfl
  rw [pow_add, mul_pow, hr, mul_one, ← pow_mul, Nat.mul_comm, pow_mul, hroot]

private noncomputable def locator : F[X] := ∏ x ∈ roots, (Polynomial.X - C (domain x))

private theorem locator_degree : locator.natDegree ≤ S - 2 := by
  unfold locator
  apply (natDegree_prod_le roots (fun x => Polynomial.X - C (domain x))).trans
  simp only [natDegree_X_sub_C, sum_const, nsmul_eq_mul, mul_one, population.1,
    Nat.cast_id, le_refl]

private theorem locator_zero (x : Fin N) : locator.eval (domain x) = 0 ↔ x ∈ roots := by
  classical
  simp [locator, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero, domain.injective.eq_iff]

attribute [irreducible] locator quotient

private noncomputable def composeHead {K : Type} [Field K] (H f : K[X]) (s : ℕ) : K[X] :=
  H * f.comp (Polynomial.X ^ s)

attribute [irreducible] composeHead

/-- The second row of each polynomial head, including its common locator. -/
noncomputable def valuePoly (H : F[X]) (i : Fin 4) : F[X] := composeHead H (quotient i) S

private theorem degree_bounds (H f : F[X]) (s k : ℕ)
    (hH : H.natDegree ≤ s - 2) (hf : f.natDegree ≤ 7) (hsk : 1 + (s - 2) + 7 * s < k) :
    (composeHead H f s).natDegree < k ∧ (Polynomial.X * composeHead H f s).natDegree < k := by
  unfold composeHead
  have hc : (f.comp (Polynomial.X ^ s)).natDegree ≤ 7 * s := by
    calc
      _ ≤ f.natDegree * (Polynomial.X ^ s : F[X]).natDegree := natDegree_comp_le
      _ ≤ 7 * s := by rw [natDegree_X_pow]; exact Nat.mul_le_mul_right _ hf
  have hv := (natDegree_mul_le (p := H) (q := f.comp (Polynomial.X ^ s))).trans
    (Nat.add_le_add hH hc)
  have hx := natDegree_mul_le (p := (Polynomial.X : F[X])) (q := H * f.comp (Polynomial.X ^ s))
  rw [natDegree_X] at hx
  omega

/-- Both rows of every head have degree strictly below the prize dimension. -/
theorem degrees (H : F[X]) (hH : H.natDegree ≤ S - 2) (i : Fin 4) :
    (valuePoly H i).natDegree < 536870912 ∧
      (Polynomial.X * valuePoly H i).natDegree < 536870912 := by
  have budget : 1 + (S - 2) + 7 * S < 536870912 := by decide
  exact degree_bounds H (quotient i) S 536870912 hH (quotient_degree i) budget

private theorem value_eval (H : F[X]) (u : Grid) (i : Fin 4) :
    (valuePoly H i).eval (domain (index u)) =
      H.eval (domain (index u)) * head omega i (omega ^ u.1.val) := by
  unfold valuePoly composeHead
  rw [eval_mul, eval_comp, eval_pow, eval_X, domain_power u, quotient_eval]

private def action (u : Grid) : Slot := slot u.1 (decide (cut u.1 ≤ u.2.val))

noncomputable def background (H : F[X]) (x : Fin N) : F := match action (index.symm x) with
  | .ordinary h => (valuePoly H h).eval (domain x)
  | _ => 0

private theorem root_mem (u : Grid) : index u ∈ roots ↔ action u = .root := by
  simpa only [roots, rootSel, action, decide_eq_true_eq] using mem_selected rootSel u

private theorem off_mem (u : Grid) : index u ∈ special ↔ action u = .off := by
  simpa only [special, offSel, action, decide_eq_true_eq] using mem_selected offSel u

private theorem ordinary_mem (u : Grid) : index u ∈ ordinary ↔ ∃ h, action u = .ordinary h := by
  rw [ordinary, mem_selected]
  change (match action u with | .ordinary _ => true | _ => false) = true ↔ _
  cases action u <;> simp

private theorem core_mem (u : Grid) (i : Fin 4) : index u ∈ core i ↔
    action u = .root ∨ ∃ h, action u = .ordinary h ∧ classID u.1 i = classID u.1 h := by
  rw [core, mem_selected]
  change (match action u with
    | .root => true
    | .off => false
    | .ordinary h => decide (classID u.1 i = classID u.1 h)) = true ↔ _
  cases action u <;> simp

/-- Every core coordinate agrees with its head on the background word. -/
theorem core_agrees (H : F[X]) (hz : ∀ x, H.eval (domain x) = 0 ↔ x ∈ roots)
    (i : Fin 4) (x : Fin N) (hx : x ∈ core i) :
    (valuePoly H i).eval (domain x) = background H x := by
  obtain ⟨u, rfl⟩ := index.surjective x
  rcases (core_mem u i).mp hx with h | ⟨j, h, hij⟩
  · have hl := (hz _).mpr ((root_mem u).mpr h)
    simp [value_eval, hl, background, h]
  · have he := (equality_class_table u.1 i j).mpr hij
    simp [background, h, value_eval, he]

theorem disjoint : Disjoint ordinary special := by
  apply Finset.disjoint_left.mpr
  rintro x ho hs
  obtain ⟨u, rfl⟩ := index.surjective x
  rcases (ordinary_mem u).mp ho with ⟨i, hi⟩
  simpa [hi] using (off_mem u).mp hs

theorem core_disjoint (i : Fin 4) : Disjoint (core i) special := by
  apply Finset.disjoint_left.mpr
  rintro x hc hs
  obtain ⟨u, rfl⟩ := index.surjective x
  have ho := (off_mem u).mp hs
  simp [core_mem, ho] at hc

private theorem ordinary_classes : ∀ j b h, slot j b = .ordinary h →
    ∃ i, classID j i ≠ classID j h := by decide

private theorem off_classes : ∀ j b, slot j b = .off → Function.Injective (classID j) := by
  decide

theorem ordinary_mismatch (H : F[X]) (hz : ∀ x, H.eval (domain x) = 0 ↔ x ∈ roots)
    (x : Fin N) (hx : x ∈ ordinary) :
    ∃ i : Fin 4, (valuePoly H i).eval (domain x) ≠ background H x := by
  obtain ⟨u, rfl⟩ := index.surjective x
  obtain ⟨h, hh⟩ := (ordinary_mem u).mp hx
  obtain ⟨i, hi⟩ := ordinary_classes _ _ _ hh
  have hloc : H.eval (domain (index u)) ≠ 0 := by simp [hz, root_mem, hh]
  refine ⟨i, ?_⟩
  simpa [background, hh, value_eval, hloc, equality_class_table] using hi

theorem special_distinct (H : F[X]) (hz : ∀ x, H.eval (domain x) = 0 ↔ x ∈ roots)
    (x : Fin N) (hx : x ∈ special) :
    Function.Injective (fun i : Fin 4 => (valuePoly H i).eval (domain x)) := by
  obtain ⟨u, rfl⟩ := index.surjective x
  have hh := (off_mem u).mp hx
  have hloc : H.eval (domain (index u)) ≠ 0 := by simp [hz, root_mem, hh]
  intro i j he
  apply off_classes _ _ hh
  simpa [value_eval, hloc, equality_class_table] using he

private noncomputable def allocationOf (H : F[X]) (hH : H.natDegree ≤ S - 2)
    (hz : ∀ x, H.eval (domain x) = 0 ↔ x ∈ roots) :
    FourHeadWitness.Allocation FourHeadWitness.firstDomain (2 ^ 29)
      ((313174699 : ℝ≥0) / 2 ^ 30) where
  head := valuePoly H
  background := background H
  ordinary := ordinary
  special := special
  core := core
  degree_head i := degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (degrees H hH i).1)
  degree_first i := degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (degrees H hH i).2)
  disjoint := disjoint
  core_disjoint := core_disjoint
  core_agrees := core_agrees H hz
  core_rank i := by
    rw [population.2.2 i]
    fin_cases i <;> decide
  core_size i := by
    rw [Fintype.card_fin, population.2.2 i]
    rw [← NNReal.coe_le_coe]
    have hδ : (313174699 : ℝ≥0) / 2 ^ 30 ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by norm_num)
    rw [NNReal.coe_mul, NNReal.coe_sub hδ]
    push_cast
    fin_cases i <;> norm_num [N]
  ordinary_mismatch := ordinary_mismatch H hz
  special_distinct := special_distinct H hz

private theorem allocation_exists :
    ∃ A : FourHeadWitness.Allocation FourHeadWitness.firstDomain (2 ^ 29)
      ((313174699 : ℝ≥0) / 2 ^ 30), A.count = 2 ^ 30 + 1 := by
  obtain ⟨H, hH, hz⟩ : ∃ H : F[X], H.natDegree ≤ S - 2 ∧
      ∀ x, H.eval (domain x) = 0 ↔ x ∈ roots := ⟨locator, locator_degree, locator_zero⟩
  refine ⟨allocationOf H hH hz, ?_⟩
  change ordinary.card + 4 * special.card = 2 ^ 30 + 1
  exact population.2.1

open ArkLib.ProximityGap.KKH26 (evalCode)

/-- The named prime crosses the 128-bit MCA budget at 313174699 errors at half rate. -/
theorem over_budget :
    (epsStar : ℝ≥0∞) < epsMCA (F := F) (evalCode generator (2 ^ 30) (2 ^ 29 - 1))
      ((313174699 : ℝ≥0) / 2 ^ 30) := by
  obtain ⟨A, hA⟩ := allocation_exists
  exact FourHeadWitness.firstPrime_bad A hA

/-- An unconditional upper bound for the operational supremum on the named subgroup. -/
theorem threshold_le :
    MCAThresholdLedger.mcaDeltaStar (F := F) (evalCode generator (2 ^ 30) (2 ^ 29 - 1))
      (epsStar : ℝ≥0∞) ≤ (313174699 : ℝ≥0) / 2 ^ 30 := by
  obtain ⟨A, hA⟩ := allocation_exists
  exact FourHeadWitness.firstPrime_upper A hA

#print axioms over_budget
#print axioms threshold_le

end ProximityGap.FirstPrimeSepticCores
