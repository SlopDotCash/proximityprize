/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases

/-! # Error patterns of four close words after puncturing one site -/

namespace ProximityGap.PuncturedFourWordProfile
open Finset Polynomial
variable {I : Type*} [Fintype I] [DecidableEq I]

private def flag (p : Prop) [Decidable p] : ℕ := if p then 1 else 0

/-- Number of the four error sets containing a coordinate. -/
def multiplicity (E : Fin 4 → Finset I) (x : I) : ℕ :=
  flag (x ∈ E 0) + flag (x ∈ E 1) + flag (x ∈ E 2) + flag (x ∈ E 3)

/-- Number of coordinates belonging to exactly j of the error sets. -/
def level (E : Fin 4 → Finset I) (j : ℕ) : ℕ :=
  (univ.filter (fun x ↦ multiplicity E x = j)).card

omit [Fintype I] in
private theorem local_counts (E : Fin 4 → Finset I) (x : I) :
    (flag (x ∈ E 0 ∪ E 1) + flag (x ∈ E 0 ∪ E 2) + flag (x ∈ E 0 ∪ E 3) +
      flag (x ∈ E 1 ∪ E 2) + flag (x ∈ E 1 ∪ E 3) + flag (x ∈ E 2 ∪ E 3) +
      flag (multiplicity E x = 0) + flag (multiplicity E x = 3) +
      3 * flag (multiplicity E x = 4) = 2 * multiplicity E x + 1) ∧
    (multiplicity E x + flag (multiplicity E x = 0) = 1 + flag (multiplicity E x = 2) +
      2 * flag (multiplicity E x = 3) + 3 * flag (multiplicity E x = 4)) := by
  by_cases ha : x ∈ E 0 <;> by_cases hb : x ∈ E 1 <;> by_cases hc : x ∈ E 2 <;>
    by_cases hd : x ∈ E 3 <;> simp [multiplicity, flag, ha, hb, hc, hd]

/-- On 4h−1 coordinates at distance at most h+1 from four words of pairwise
distance at least 2h+1, the only possible (zero-, two-, three-error) counts are
(0,5,0), (1,6,0) and (0,3,1). Every word has h+1 errors. -/
theorem classify (E : Fin 4 → Finset I) (h : ℕ) (hn : Fintype.card I + 1 = 4*h)
    (hw : ∀ i, (E i).card ≤ h+1)
    (hd : ∀ i j, i ≠ j → 2*h+1 ≤ (E i ∪ E j).card) :
    (∀ i, (E i).card = h+1) ∧ level E 4 = 0 ∧
    ((level E 0 = 0 ∧ level E 2 = 5 ∧ level E 3 = 0) ∨
     (level E 0 = 1 ∧ level E 2 = 6 ∧ level E 3 = 0) ∨
     (level E 0 = 0 ∧ level E 2 = 3 ∧ level E 3 = 1)) := by
  classical
  have hs (S : Finset I) : (∑ x : I, flag (x ∈ S)) = S.card := by simp [flag]
  have hl (j : ℕ) : (∑ x : I, flag (multiplicity E x = j)) = level E j := by
    simp [flag, level]
  have hm : (∑ x : I, multiplicity E x) =
      (E 0).card + (E 1).card + (E 2).card + (E 3).card := by
    simp only [multiplicity, sum_add_distrib, hs]
  have pair_count := sum_congr (rfl : (univ : Finset I) = univ) fun x _ ↦ (local_counts E x).1
  have error_count := sum_congr (rfl : (univ : Finset I) = univ) fun x _ ↦ (local_counts E x).2
  simp only [sum_add_distrib, ← mul_sum, hs, hl, hm, sum_const, card_univ, nsmul_eq_mul,
    mul_one, Nat.cast_id] at pair_count error_count
  have h01 := hd 0 1 (by decide)
  have h02 := hd 0 2 (by decide)
  have h03 := hd 0 3 (by decide)
  have h12 := hd 1 2 (by decide)
  have h13 := hd 1 3 (by decide)
  have h23 := hd 2 3 (by decide)
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  have h3 := hw 3
  have all_pairs : 12*h+6 ≤ (E 0 ∪ E 1).card + (E 0 ∪ E 2).card + (E 0 ∪ E 3).card +
      (E 1 ∪ E 2).card + (E 1 ∪ E 3).card + (E 2 ∪ E 3).card := by omega
  clear h01 h02 h03 h12 h13 h23
  have mass : 4 * (h+1) ≤ (E 0).card + (E 1).card + (E 2).card + (E 3).card := by omega
  constructor
  · intro i
    fin_cases i
    · change (E 0).card = h+1; omega
    · change (E 1).card = h+1; omega
    · change (E 2).card = h+1; omega
    · change (E 3).card = h+1; omega
  · omega

omit [Fintype I] [DecidableEq I] in
/-- Two polynomials already agreeing on their entire degree allowance cannot
agree at a further field point. -/
theorem separate_outside {F : Type*} [Field F] [DecidableEq F]
    (D : I ↪ F) (u v : F[X]) (S : Finset I) (a : F) (ha : a ∉ Set.range D)
    (huv : u ≠ v) (hu : u.natDegree ≤ S.card) (hv : v.natDegree ≤ S.card)
    (hs : ∀ x ∈ S, u.eval (D x) = v.eval (D x)) : u.eval a ≠ v.eval a := by
  classical
  intro he
  let T := insert a (S.image D)
  have hn : a ∉ S.image D := by
    intro hm
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ha ⟨j, hj⟩
  have hT : T.card = S.card + 1 := by
    simp [T, hn, card_image_of_injective _ D.injective]
  apply huv
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq u v (f := fun x : T ↦ x.val)
    Subtype.val_injective
  · intro x
    have hx := x.property
    change x.val ∈ insert a (S.image D) at hx
    rcases mem_insert.mp hx with h | h
    · simpa [h] using he
    · obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp h
      simpa [← hjx] using hs j hj
  · rw [Fintype.card_coe, hT]
    exact max_lt (by omega) (by omega)

/-- Pairwise error unions at the punctured dimension and list radius automatically
meet the distance hypotheses in the finite classification. -/
theorem error_union {F : Type*} [Field F] [DecidableEq F]
    (D : I ↪ F) (u v : F[X]) (w : I → F) (h : ℕ) (hn : Fintype.card I + 1 = 4*h)
    (huv : u ≠ v) (hu : u.natDegree + 2 ≤ 2*h) (hv : v.natDegree + 2 ≤ 2*h) :
    2*h+1 ≤ ((univ.filter (fun x : I ↦ u.eval (D x) ≠ w x)) ∪
      (univ.filter (fun x : I ↦ v.eval (D x) ≠ w x))).card := by
  classical
  let E := (univ.filter (fun x : I ↦ u.eval (D x) ≠ w x)) ∪
    (univ.filter (fun x : I ↦ v.eval (D x) ≠ w x))
  let S := (univ : Finset I) \ E
  change 2*h+1 ≤ E.card
  by_contra! hsmall
  have hS : S.card + E.card = Fintype.card I := by
    rw [show S.card = (univ : Finset I).card - E.card from card_sdiff_of_subset (subset_univ _)]
    have hle := card_le_card (subset_univ E)
    simpa using Nat.sub_add_cancel hle
  apply huv
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq u v (f := fun x : S ↦ D x.val)
    (D.injective.comp Subtype.val_injective)
  · intro x
    have hx := (Finset.mem_sdiff.mp x.property).2
    simp [E] at hx
    exact hx.1.trans hx.2.symm
  · rw [Fintype.card_coe]
    exact max_lt (by omega) (by omega)

/-- The three exact patterns for four distinct Reed–Solomon messages on the
punctured domain, evaluated against their actual common received word. -/
theorem polynomial_profile {F : Type*} [Field F] [DecidableEq F]
    (D : I ↪ F) (P : Fin 4 → F[X]) (w : I → F) (h : ℕ) (hn : Fintype.card I + 1 = 4*h)
    (hi : Function.Injective P) (hp : ∀ i, (P i).natDegree + 2 ≤ 2*h)
    (hw : ∀ i, (univ.filter (fun x : I ↦ (P i).eval (D x) ≠ w x)).card ≤ h+1) :
    let E := fun i ↦ univ.filter (fun x : I ↦ (P i).eval (D x) ≠ w x)
    (∀ i, (E i).card = h+1) ∧ level E 4 = 0 ∧
    ((level E 0 = 0 ∧ level E 2 = 5 ∧ level E 3 = 0) ∨
     (level E 0 = 1 ∧ level E 2 = 6 ∧ level E 3 = 0) ∨
     (level E 0 = 0 ∧ level E 2 = 3 ∧ level E 3 = 1)) :=
  classify _ h hn hw fun i j hij ↦ error_union D _ _ w h hn (hi.ne hij) (hp i) (hp j)

#print axioms polynomial_profile
#print axioms classify
#print axioms separate_outside
#print axioms error_union
end ProximityGap.PuncturedFourWordProfile
