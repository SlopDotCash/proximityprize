/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# Packing six-rich points of affine-function arrangements

Let thirteen coordinate functions be indexed by `I`.  Suppose every equality
class of identical functions has size at most three, while two nonidentical
functions can agree at at most one parameter.  Then at most eight
parameter-value points are incident with six or more coordinate functions.

The count keeps only ordered pairs of nonidentical functions through a rich
point.  Each six-rich point owns at least eighteen such pairs: for each of its
six incident functions, at most two of the other five are identical.  Distinct
rich points own disjoint pairs, and there are only `13 * 12 = 156` ordered
distinct coordinate pairs.  Hence `18 M <= 156`, so `M <= 8`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

open Finset

namespace ArkLib.ProximityGap.Frontier.AffineRichPointPacking

attribute [local instance] Classical.propDecidable

variable {I Gamma V : Type} [Fintype I] [DecidableEq I]
variable [Fintype Gamma] [DecidableEq Gamma]
variable [Fintype V] [DecidableEq V]

/-- Indices of coordinate functions incident with a parameter-value point. -/
def incidence (phi : I → Gamma → V) (p : Gamma × V) : Finset I :=
  Finset.univ.filter fun i ↦ phi i p.1 = p.2

/-- All parameter-value points incident with at least `t` functions. -/
def richPoints (phi : I → Gamma → V) (t : Nat) : Finset (Gamma × V) :=
  Finset.univ.filter fun p ↦ t ≤ (incidence phi p).card

/-- The equality class of a coordinate function. -/
def equalFunctionClass (phi : I → Gamma → V) (i : I) : Finset I :=
  Finset.univ.filter fun j ↦ phi j = phi i

/-- Other incident indices whose coordinate function is genuinely different. -/
def differentPartners (phi : I → Gamma → V)
    (p : Gamma × V) (i : I) : Finset I :=
  ((incidence phi p).erase i).filter fun j ↦ phi j ≠ phi i

/-- Ordered pairs of nonidentical coordinate functions owned by one point. -/
def ownedPairs (phi : I → Gamma → V)
    (p : Gamma × V) : Finset (I × I) :=
  (incidence phi p).biUnion fun i ↦
    (differentPartners phi p i).image fun j ↦ (i, j)

@[simp]
theorem mem_incidence_iff (phi : I → Gamma → V)
    (p : Gamma × V) (i : I) :
    i ∈ incidence phi p ↔ phi i p.1 = p.2 := by
  simp [incidence]

@[simp]
theorem mem_equalFunctionClass_iff (phi : I → Gamma → V)
    (i j : I) :
    j ∈ equalFunctionClass phi i ↔ phi j = phi i := by
  simp [equalFunctionClass]

/-- At a six-rich point, every incident coordinate has at least three
genuinely different incident partners. -/
theorem three_le_differentPartners_card
    (phi : I → Gamma → V)
    (heqClass : ∀ i, (equalFunctionClass phi i).card ≤ 3)
    {p : Gamma × V} (hrich : 6 ≤ (incidence phi p).card)
    {i : I} (hi : i ∈ incidence phi p) :
    3 ≤ (differentPartners phi p i).card := by
  let A := incidence phi p
  let B := A.erase i
  let same := B.filter fun j ↦ phi j = phi i
  let diff := B.filter fun j ↦ phi j ≠ phi i
  have hBcard : B.card = A.card - 1 := by
    simpa only [B] using Finset.card_erase_of_mem hi
  have hiClass : i ∈ equalFunctionClass phi i := by simp
  have hclassErase : ((equalFunctionClass phi i).erase i).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hiClass]
    have hcap := heqClass i
    omega
  have hsameSub : same ⊆ (equalFunctionClass phi i).erase i := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hjData.1).1,
        (mem_equalFunctionClass_iff phi i j).mpr hjData.2⟩
  have hsame : same.card ≤ 2 :=
    (Finset.card_le_card hsameSub).trans hclassErase
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := B) (p := fun j ↦ phi j = phi i)
  have hpartition' : same.card + diff.card = B.card := by
    simpa only [same, diff, ne_eq] using hpartition
  change 3 ≤ diff.card
  change 6 ≤ A.card at hrich
  omega

/-- A six-rich point owns at least eighteen ordered pairs of nonidentical
coordinate functions. -/
theorem eighteen_le_ownedPairs_card
    (phi : I → Gamma → V)
    (heqClass : ∀ i, (equalFunctionClass phi i).card ≤ 3)
    {p : Gamma × V} (hrich : 6 ≤ (incidence phi p).card) :
    18 ≤ (ownedPairs phi p).card := by
  let A := incidence phi p
  let fiber : I → Finset (I × I) := fun i ↦
    (differentPartners phi p i).image fun j ↦ (i, j)
  have hdisj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (fiber i) (fiber j) := by
    intro i _hi j _hj hij
    rw [Finset.disjoint_left]
    intro pair hpairI hpairJ
    obtain ⟨x, _hx, hpairIeq⟩ := Finset.mem_image.mp hpairI
    obtain ⟨y, _hy, hpairJeq⟩ := Finset.mem_image.mp hpairJ
    apply hij
    have hfirst := congrArg Prod.fst (hpairIeq.trans hpairJeq.symm)
    simpa using hfirst
  have hcard : (ownedPairs phi p).card =
      ∑ i ∈ A, (differentPartners phi p i).card := by
    rw [ownedPairs, show incidence phi p = A from rfl,
      Finset.card_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro i _hi
    exact Finset.card_image_of_injective _ fun _ _ h ↦
      congrArg Prod.snd h
  rw [hcard]
  calc
    18 ≤ A.card * 3 := by
      change 6 ≤ A.card at hrich
      omega
    _ = ∑ _i ∈ A, 3 := by simp
    _ ≤ ∑ i ∈ A, (differentPartners phi p i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact three_le_differentPartners_card phi heqClass hrich hi

/-- Different rich points own disjoint ordered pairs, because two
nonidentical functions have at most one common parameter. -/
theorem ownedPairs_disjoint_of_ne
    (phi : I → Gamma → V)
    (hcross : ∀ i j, phi i ≠ phi j →
      ∀ gamma beta,
        phi i gamma = phi j gamma →
        phi i beta = phi j beta → gamma = beta)
    {p q : Gamma × V} (hpq : p ≠ q) :
    Disjoint (ownedPairs phi p) (ownedPairs phi q) := by
  rw [Finset.disjoint_left]
  intro pair hpairP hpairQ
  rw [ownedPairs, Finset.mem_biUnion] at hpairP hpairQ
  obtain ⟨i, hiP, hpairP⟩ := hpairP
  obtain ⟨i', hiQ, hpairQ⟩ := hpairQ
  rw [Finset.mem_image] at hpairP hpairQ
  obtain ⟨j, hjP, hpEq⟩ := hpairP
  obtain ⟨j', hjQ, hqEq⟩ := hpairQ
  have hii' : i = i' := by
    have h := congrArg Prod.fst (hpEq.trans hqEq.symm)
    simpa using h
  have hjj' : j = j' := by
    have h := congrArg Prod.snd (hpEq.trans hqEq.symm)
    simpa using h
  subst i'
  subst j'
  have hjPData := Finset.mem_filter.mp hjP
  have hphiNe : phi j ≠ phi i := hjPData.2
  have hiPval : phi i p.1 = p.2 := (mem_incidence_iff phi p i).mp hiP
  have hiQval : phi i q.1 = q.2 := (mem_incidence_iff phi q i).mp hiQ
  have hjPInc : j ∈ incidence phi p := (Finset.mem_erase.mp hjPData.1).2
  have hjQData := Finset.mem_filter.mp hjQ
  have hjQInc : j ∈ incidence phi q := (Finset.mem_erase.mp hjQData.1).2
  have hjPval : phi j p.1 = p.2 := (mem_incidence_iff phi p j).mp hjPInc
  have hjQval : phi j q.1 = q.2 := (mem_incidence_iff phi q j).mp hjQInc
  have hparam : p.1 = q.1 := hcross j i hphiNe p.1 q.1
    (hjPval.trans hiPval.symm) (hjQval.trans hiQval.symm)
  have hvalue : p.2 = q.2 := by rw [← hiPval, ← hiQval, hparam]
  exact hpq (Prod.ext hparam hvalue)

/-- Every owned pair is an ordered pair of distinct coordinate indices. -/
theorem ownedPairs_subset_offDiag
    (phi : I → Gamma → V) (p : Gamma × V) :
    ownedPairs phi p ⊆ (Finset.univ : Finset I).offDiag := by
  intro pair hpair
  rw [ownedPairs, Finset.mem_biUnion] at hpair
  obtain ⟨i, _hi, hpair⟩ := hpair
  rw [Finset.mem_image] at hpair
  obtain ⟨j, hj, rfl⟩ := hpair
  have hne : j ≠ i := (Finset.mem_erase.mp (Finset.mem_filter.mp hj).1).1
  simp [hne.symm]

/-- **Thirteen affine functions have at most eight six-rich points** under
the equality-class and pair-crossing hypotheses. -/
theorem richPoints_six_card_le_eight
    (phi : I → Gamma → V)
    (hI : Fintype.card I = 13)
    (heqClass : ∀ i, (equalFunctionClass phi i).card ≤ 3)
    (hcross : ∀ i j, phi i ≠ phi j →
      ∀ gamma beta,
        phi i gamma = phi j gamma →
        phi i beta = phi j beta → gamma = beta) :
    (richPoints phi 6).card ≤ 8 := by
  let R := richPoints phi 6
  let own : Gamma × V → Finset (I × I) := ownedPairs phi
  have hdisj : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → Disjoint (own p) (own q) := by
    intro p _hp q _hq hpq
    exact ownedPairs_disjoint_of_ne phi hcross hpq
  have hcardUnion : (R.biUnion own).card = ∑ p ∈ R, (own p).card :=
    Finset.card_biUnion hdisj
  have hlower : R.card * 18 ≤ ∑ p ∈ R, (own p).card := by
    calc
      R.card * 18 = ∑ _p ∈ R, 18 := by simp
      _ ≤ ∑ p ∈ R, (own p).card := by
        apply Finset.sum_le_sum
        intro p hp
        have hpRich : 6 ≤ (incidence phi p).card := by
          simpa only [R, richPoints, Finset.mem_filter,
            Finset.mem_univ, true_and] using hp
        exact eighteen_le_ownedPairs_card phi heqClass hpRich
  have hUnionSub : R.biUnion own ⊆ (Finset.univ : Finset I).offDiag := by
    rw [Finset.biUnion_subset]
    intro p _hp
    exact ownedPairs_subset_offDiag phi p
  have hupper : (R.biUnion own).card ≤ 156 := by
    calc
      (R.biUnion own).card ≤ (Finset.univ : Finset I).offDiag.card :=
        Finset.card_le_card hUnionSub
      _ = 156 := by rw [Finset.offDiag_card, Finset.card_univ, hI]
  rw [hcardUnion] at hupper
  change R.card ≤ 8
  omega

#print axioms richPoints_six_card_le_eight

end ArkLib.ProximityGap.Frontier.AffineRichPointPacking
