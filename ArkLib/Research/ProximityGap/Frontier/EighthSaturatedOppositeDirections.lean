/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FourHeadCoreDeterminant
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorRateQuarterDeterminantMultiplicity

/-! # Opposite directions limit a saturated eighth-rate quartet at 671088639 errors -/

namespace ArkLib.ProximityGap.Frontier.EighthSaturatedOppositeDirections
open Finset Polynomial _root_.ProximityGap.FourHeadCoreDeterminant

variable {F I : Type*} [Field F]

private def bit (b : Fin 4 → Bool) (i : Fin 4) : ℕ := if b i then 1 else 0

/-- The four triples, indexed by their omitted head. -/
def face : Fin 4 → Fin 3 → Fin 4 := ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- Number of the four defining cores containing one physical site. -/
def count (b : Fin 4 → Bool) := ∑ i, bit b i
/-- Vanishing order forced on the given triangle by its three core bits. -/
def charge (b : Fin 4 → Bool) (j : Fin 4) :=
  bit b (face j 0) + bit b (face j 1) + bit b (face j 2) - 1

private theorem local_layout : ∀ b : Fin 4 → Bool,
    2 * count b + (if count b = 1 ∨ count b = 2 then 0 else 1) ≤
        2 + ∑ j, charge b j := by decide

private theorem local_partition : ∀ b : Fin 4 → Bool, count b = 1 ∨ count b = 2 →
    1 + (if count b = 2 then 1 else 0) = count b ∧
    (if count b = 1 ∧ b 0 = false then 1 else 0) + bit b 0 + charge b 0 = 1 := by decide

/-- With the exact saturated core numbers, every coordinate belongs to one or
two cores. There are 4d double sites and at most 3k+6 singleton sites not
owned by the five-fresh head. Each face budget is the usual triangle bound. -/
theorem layout [Fintype I] (b : I → Fin 4 → Bool)
    (length : Fintype.card I = 1073741824)
    (core_total : (∑ x, ∑ i, if b x i then 1 else 0 : ℕ) = 1610612732)
    (fourth_core : (∑ x, if b x 0 then 1 else 0 : ℕ) = 402653180)
    (faces : ∀ j, (∑ x, ((if b x (face j 0) then 1 else 0 : ℕ) +
      (if b x (face j 1) then 1 else 0) + (if b x (face j 2) then 1 else 0) - 1)) ≤ 268435454) :
    (∀ x, count (b x) = 1 ∨ count (b x) = 2) ∧
    (univ.filter fun x => count (b x) = 2).card = 536870908 ∧
    (univ.filter fun x => count (b x) = 1 ∧ b x 0 = false).card = 402653190 := by
  classical
  change (∑ x, count (b x)) = _ at core_total
  change (∑ x, bit (b x) 0) = _ at fourth_core
  change ∀ j, (∑ x, charge (b x) j) ≤ _ at faces
  let exceptional (x : I) := if count (b x) = 1 ∨ count (b x) = 2 then 0 else 1
  have total := sum_le_sum (s := univ) (fun x _ => local_layout (b x))
  change (∑ x, (2 * count (b x) + exceptional x)) ≤ _ at total
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_comm (s := univ) (t := univ)
    (f := fun x j => charge (b x) j)] at total
  simp only [sum_const, card_univ, smul_eq_mul, length] at total
  have split : (∑ j, ∑ x, charge (b x) j) =
    (∑ x, charge (b x) 0) + (∑ x, charge (b x) 1) +
    (∑ x, charge (b x) 2) + (∑ x, charge (b x) 3) := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [split] at total
  have h₀ := faces 0
  have h₁ := faces 1
  have h₂ := faces 2
  have h₃ := faces 3
  have zero : (∑ x, exceptional x) = 0 := by omega
  have regular (x : I) : count (b x) = 1 ∨ count (b x) = 2 := by
    by_contra neg
    have one : exceptional x = 1 := by simp [exceptional, neg]
    have single := single_le_sum (f := exceptional) (fun i _ => Nat.zero_le (exceptional i))
      (mem_univ x)
    omega
  have doubles := sum_congr (s₁ := (univ : Finset I)) rfl
    (fun x _ => (local_partition (b x) (regular x)).1)
  have private_sum := sum_congr (s₁ := (univ : Finset I)) rfl
    (fun x _ => (local_partition (b x) (regular x)).2)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, length,
    sum_boole, Nat.cast_id] at doubles private_sum
  exact ⟨regular, by omega, by omega⟩

open HalfPredecessorRateQuarterDeterminantMultiplicity in
/-- The four charge inequalities for the physical core masks follow from the
actual nonzero triangle determinants and the degree bound. -/
theorem face_budgets {K : Type} [Field K] {J : Type} [Fintype J]
    (dom : J ↪ K) (u v : J → K) (W : Fin 4 → K[X] × K[X])
    (b : J → Fin 4 → Bool)
    (mask : ∀ x i, b x i = true ↔
      AgreesAt (u x) (v x) (dom x) (W i))
    (degrees : ∀ i, (W i).1.natDegree < 134217728 ∧ (W i).2.natDegree < 134217728)
    (triangles : ∀ j, threeLineDeterminant
      (W (face j 0)) (W (face j 1)) (W (face j 2)) ≠ 0) :
    ∀ j, (∑ x, charge (b x) j) ≤ 268435454 := by
  classical
  intro j
  have tri := sum_coreCount_sub_one_le_natDegree
    dom u v _ _ _ univ (triangles j)
  have degree := natDegree_threeLineDeterminant_le_two_mul_sub_two
    (degrees (face j 0)).1 (degrees (face j 0)).2 (degrees (face j 1)).1 (degrees (face j 1)).2
    (degrees (face j 2)).1 (degrees (face j 2)).2
  simpa only [charge, bit, mask, coreCount]
    using tri.trans degree

/-- Two actual finite folded labels on opposite edges satisfy the same
projective involution at every double site. -/
theorem opposite_labels {a b c z t u v p q : F}
    (hu : u + z * v = 0) (hp : p + t * q = 0) (hv : v ≠ 0) (hq : q ≠ 0)
    (form : a * (v * q) - b * (u * q + v * p) + c * (u * p) = 0) :
    a + b * (z + t) + c * z * t = 0 := by
  apply (mul_eq_zero.mp (show (a + b * (z + t) + c * z * t) * (v * q) = 0 by
    linear_combination form + (b * q - c * p) * hu + (b + c * z) * v * hp)).resolve_right
  exact mul_ne_zero hv hq

private theorem unique_opposite {a b c z t t' : F} (hn : b ^ 2 - a * c ≠ 0)
    (h : a + b * (z + t) + c * z * t = 0)
    (h' : a + b * (z + t') + c * z * t' = 0) : t = t' := by
  have nonzero : b + c * z ≠ 0 := by
    intro e
    apply hn
    linear_combination (b + c * t) * e - c * h
  have prod : (b + c * z) * (t - t') = 0 := by linear_combination h - h'
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left nonzero)

/-- The first three heads have at most 15k slots. Every fourth-head label uses
five sites, and all but the first-three singleton sites reserve an opposite
slot. Distinct occupied slots at these doubles require distinct fourth labels. -/
theorem scheduled_cap (S U : Finset (Fin 3 × I)) (T P : Finset I) (M : Finset F)
    (remaining : I → Fin 3) (first : Fin 3 × I → F) (last : I → F)
    (slots : S.card ≤ 2013265920) (used : U ⊆ S) (injective : Set.InjOn first ↑U)
    (singletons : P.card ≤ 402653190) (five : 5 * M.card ≤ T.card)
    (values : ∀ x ∈ T, last x ∈ M)
    (reserved : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ S)
    {a b c : F} (nonsingular : b ^ 2 - a * c ≠ 0)
    (partners : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ U →
      a + b * (last x + first (remaining x, x)) + c * last x * first (remaining x, x) = 0) :
    U.card + M.card ≤ 2113929217 := by
  classical
  let put : I ↪ Fin 3 × I := ⟨fun x => (remaining x, x), fun _ _ h => congrArg Prod.snd h⟩
  let D := (T \ P).map put
  have sub : D ⊆ S := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
    exact reserved x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2
  have source {s : Fin 3 × I} (hs : s ∈ D) : s.2 ∈ T ∧ s.2 ∉ P ∧ (remaining s.2, s.2) = s := by
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
    exact ⟨(mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2, rfl⟩
  have eqn {s : Fin 3 × I} (hs : s ∈ D ∩ U) :
      a + b * (last s.2 + first s) + c * last s.2 * first s = 0 := by
    obtain ⟨hD, hU⟩ := mem_inter.mp hs
    obtain ⟨hT, hP, he⟩ := source hD
    have h := partners s.2 hT hP (he.symm ▸ hU)
    rwa [he] at h
  have overlap : (D ∩ U).card ≤ M.card := by
    apply card_le_card_of_injOn (fun s => last s.2)
    · exact fun s hs => values s.2 (source (mem_inter.mp hs).1).1
    · intro s hs u hu he
      apply injective (mem_inter.mp hs).2 (mem_inter.mp hu).2
      apply unique_opposite nonsingular (eqn hs)
      rw [show last s.2 = last u.2 from he]
      exact eqn hu
  have union_bound := card_le_card (union_subset sub used)
  have inclusion := card_union_add_card_inter D U
  have common := card_sdiff_add_card_inter T P
  have small := card_le_card (inter_subset_right (s₁ := T) (s₂ := P))
  have occupied := card_le_card used
  have hD : D.card = (T \ P).card := card_map _
  omega

/-- On an actual saturated polynomial quartet the global direction form supplies
the unique opposite label used in the slot bound. Number the five-fresh head
zero, and the three one-fresh heads one through three. -/
theorem saturated_cap (A B : Fin 4 → F[X]) (d : ℕ) (E : Finset F)
    (hA : ∀ i, (A i).natDegree ≤ d) (hB : ∀ i, (B i).natDegree ≤ d)
    (htr : triangle A B 0 1 2 * triangle A B 0 1 3 *
      triangle A B 0 2 3 * triangle A B 1 2 3 ≠ 0)
    (hE : E.card = 4 * d)
    (hfit : ∀ x ∈ E, ∃ (O : Finset (Fin 4)) (u v : F), O.card = 2 ∧
      ∀ i ∈ O, (A i).eval x = u ∧ (B i).eval x = v)
    (dom : I → F) (S U : Finset (Fin 3 × I)) (T P : Finset I) (M : Finset F)
    (remaining facing : I → Fin 3) (first : Fin 3 × I → F) (last : I → F)
    (slots : S.card ≤ 2013265920) (used : U ⊆ S) (injective : Set.InjOn first ↑U)
    (singletons : P.card ≤ 402653190) (five : 5 * M.card ≤ T.card)
    (values : ∀ x ∈ T, last x ∈ M)
    (reserved : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ S)
    (folds : ∀ x ∈ T, x ∉ P → (remaining x, x) ∈ U →
      let j := facing x
      (nearSide B j).eval (dom x) ≠ 0 ∧ (farSide B j).eval (dom x) ≠ 0 ∧
      (nearSide A j).eval (dom x) + last x * (nearSide B j).eval (dom x) = 0 ∧
      (farSide A j).eval (dom x) + first (remaining x, x) * (farSide B j).eval (dom x) = 0) :
    U.card + M.card + 20607410 ≤ 2134536627 := by
  obtain ⟨a, b, c, hn, form⟩ := saturated_direction_form A B d hA hB htr E hE hfit
  have bound := scheduled_cap S U T P M remaining first last slots used injective singletons five
    values reserved hn (fun x hx hp hu => by
      obtain ⟨hv, hq, hz, ht⟩ := folds x hx hp hu
      apply opposite_labels hz ht hv hq
      have h := congrArg (Polynomial.eval (dom x)) (form (facing x))
      simpa only [eval_zero, eval_add, eval_sub, eval_mul, eval_C] using h)
  omega

#print axioms layout
#print axioms face_budgets
#print axioms saturated_cap
end ArkLib.ProximityGap.Frontier.EighthSaturatedOppositeDirections
