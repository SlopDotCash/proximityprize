/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! # Universal planar meeting-excess sharpness and quotient-free MCA barriers

This standalone Mathlib-only module proves three universal algebraic and combinatorial
sharpness/barrier theorems governing simultaneous-label MCA upper-bound constructions
across all fields and evaluation domains:

1. **Universal `4 d` Meeting-Excess Theorem (`four_noncollinear_meeting_excess_le`):**
   Over **any** field `F` (any characteristic), any four pairwise-distinct non-collinear
   polynomial pairs `(U_i, V_i) ∈ F[X]_{≤ d}^2` satisfy
   `∑ x ∈ S, (4 - |{(U_i(x), V_i(x)) : i ∈ Fin 4}|) ≤ 4 * d`
   on every finite evaluation set `S ⊆ F`.
   - At `d = 3` (`four_noncollinear_cubics_le_twelve`), this yields `≤ 12`, proving that both
     `SecondPrimePlanarQuartet.lean` (`553,648,129` on `p2` quarter-rate) and
     `EighthTransverseAttack.lean` (`679,477,248` on `p2` eighth-rate) attain the universal
     maximum `12` among all four-cubic planar arrangements.
   - At `d = 7` (`four_noncollinear_septics_le_28`), this yields `≤ 28`, matching the
     saturation ceiling on `μ_32`.

2. **Universal Quotient-Free Label-Core Conservation & `H`-Count Barriers:**
   Without any quotient, rank, or field-structure assumption:
   - `label_core_conservation` (`H * c + L ≤ H * n`) and `discrete_johnson_hull`
     (`2 * a * H * c ≤ H * (H - 1) * d + a * (a + 1) * Cov.card`) plus `continuous_johnson_hull`
     (`(H * c)^2 ≤ Cov.card * (H * c + H * (H - 1) * d)`).
   - On `p2` (`B = 2^31`): `H ≤ 4` forces `e ≥ 536,870,912` (`1/2 n`), `H = 5` forces
     `e ≥ 429,496,729`, and `H = 6` forces `e ≥ 357,913,941` (so breaking
     `< 357,913,941` on `p2` half-rate unconditionally requires `H ≥ 7`).
   - On `p1` quarter-rate (`d = 2^28 - 1, B = 2^30`): **every** `H ≥ 5` 1-fresh witness (both
     2D planar and 1D collinear) is forced to `e ≥ 483,183,821 > 480,946,859`.
   - On `p2` eighth-rate (`d = 2^27 - 1, B = 2^31`): **every** 1D collinear 1-fresh witness
     of **any** head count `H ≥ 2` is forced to `e ≥ 683,871,281 > 679,477,248`.

3. **Global Full-Rank Optimality of `SecondPrimeCyclicCubics` (`380,283,564`):**
   Every full-rank 2D planar quotient arrangement (`M ≥ 8, H ≥ 4, D ≥ 1, E ≤ (H-1)(D+1) - 2`)
   satisfies `C_tot + 3 ≤ H * (K + 1) + (M - K)`, proving that `M = 8, D = 3, H = 6`
   (`31/48`, realized by `SecondPrimeCyclicCubics.lean` at `380,283,564`) strictly dominates
   every other `(M, H)` full-rank 2D planar parameter choice on `p2` half-rate.
-/

set_option autoImplicit false
noncomputable section

namespace ArkLib.ProximityGap.Frontier.PlanarSharpnessAndBarriers

open Finset Polynomial

/-! ## Part 1: Universal `4 * d` meeting-excess theorem for four non-collinear pairs -/

section FourNoncollinear

variable {F : Type*} [Field F] [DecidableEq F]

/-- Oriented `2 × 2` determinant of three polynomial pairs in `F[X]^2`. -/
def det3 (U V : Fin 4 → F[X]) (i j k : Fin 4) : F[X] :=
  (U j - U i) * (V k - V i) - (U k - U i) * (V j - V i)

/-- Number of distinct evaluated pairs among `Fin 4` at `x : F`. -/
def distinctAt (U V : Fin 4 → F[X]) (x : F) : ℕ :=
  (univ.image fun i : Fin 4 => ((U i).eval x, (V i).eval x)).card

/-- Meeting excess `4 - distinctAt U V x = ∑_C (|C| - 1)` at `x : F`. -/
def meetingExcess (U V : Fin 4 → F[X]) (x : F) : ℕ :=
  4 - distinctAt U V x

private theorem meetingExcess_perm (U V : Fin 4 → F[X]) (σ : Equiv.Perm (Fin 4)) (x : F) :
    meetingExcess (U ∘ σ) (V ∘ σ) x = meetingExcess U V x := by
  unfold meetingExcess distinctAt
  congr 1
  have himg : (univ.image fun i : Fin 4 => ((U (σ i)).eval x, (V (σ i)).eval x)) =
      (univ.image fun i : Fin 4 => ((U i).eval x, (V i).eval x)) := by
    ext p
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨σ.symm j, by simp⟩
  exact congrArg Finset.card himg

omit [DecidableEq F] in
private theorem natDegree_sub_le_same {d : ℕ} {p q : F[X]}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) : (p - q).natDegree ≤ d :=
  (natDegree_sub_le_of_le hp hq).trans_eq (max_self d)

omit [DecidableEq F] in
private theorem natDegree_det3_le {d : ℕ} (U V : Fin 4 → F[X])
    (hU : ∀ i, (U i).natDegree ≤ d) (hV : ∀ i, (V i).natDegree ≤ d) (i j k : Fin 4) :
    (det3 U V i j k).natDegree ≤ 2 * d := by
  unfold det3
  have h1 : ((U j - U i) * (V k - V i)).natDegree ≤ 2 * d :=
    natDegree_mul_le.trans (by
      have := natDegree_sub_le_same (hU j) (hU i)
      have := natDegree_sub_le_same (hV k) (hV i)
      omega)
  have h2 : ((U k - U i) * (V j - V i)).natDegree ≤ 2 * d :=
    natDegree_mul_le.trans (by
      have := natDegree_sub_le_same (hU k) (hU i)
      have := natDegree_sub_le_same (hV j) (hV i)
      omega)
  exact natDegree_sub_le_same h1 h2

private theorem sum_rootMultiplicity_le_natDegree (p : F[X]) (_hp : p ≠ 0) (S : Finset F) :
    ∑ x ∈ S, p.rootMultiplicity x ≤ p.natDegree := by
  have hcnt : ∑ x ∈ S, p.roots.count x ≤ p.roots.card := by
    have h1 : ∑ x ∈ S, p.roots.count x = (p.roots.filter (· ∈ S)).card := by
      classical
      induction S using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, ih]
        have hpart : p.roots.filter (· ∈ insert a s) =
            p.roots.filter (· = a) + p.roots.filter (· ∈ s) := by
          ext y
          rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter,
            Multiset.count_filter]
          by_cases hya : y = a
          · subst hya; simp [ha]
          · simp [hya]
        have hcomm : p.roots.filter (fun x => x = a) = p.roots.filter (fun x => a = x) := by
          congr 1; funext x; exact propext eq_comm
        rw [hpart, Multiset.card_add, hcomm, Multiset.count_eq_card_filter_eq]
    rw [h1]
    exact Multiset.card_le_card (Multiset.filter_le _ _)
  calc ∑ x ∈ S, p.rootMultiplicity x
      = ∑ x ∈ S, p.roots.count x := by
          refine Finset.sum_congr rfl fun x _ => (Polynomial.count_roots p).symm
    _ ≤ p.roots.card := hcnt
    _ ≤ p.natDegree := Polynomial.card_roots' p

private theorem sum_eval_zero_le_natDegree (p : F[X]) (hp : p ≠ 0) (S : Finset F) :
    ∑ x ∈ S, (if p.eval x = 0 then 1 else 0) ≤ p.natDegree := by
  have hle : ∀ x ∈ S, (if p.eval x = 0 then 1 else 0) ≤ p.rootMultiplicity x := by
    intro x _
    split_ifs with hz
    · exact (Polynomial.le_rootMultiplicity_iff hp).mpr (by
        rw [pow_one]
        exact Polynomial.dvd_iff_isRoot.mpr hz)
    · exact Nat.zero_le _
  exact (Finset.sum_le_sum hle).trans (sum_rootMultiplicity_le_natDegree p hp S)

omit [DecidableEq F] in
private theorem rootMult_ge_one_of_eq (U V : Fin 4 → F[X]) (i j k : Fin 4)
    (hdet : det3 U V i j k ≠ 0) (x : F)
    (h : ((U i).eval x = (U j).eval x ∧ (V i).eval x = (V j).eval x) ∨
         ((U i).eval x = (U k).eval x ∧ (V i).eval x = (V k).eval x) ∨
         ((U j).eval x = (U k).eval x ∧ (V j).eval x = (V k).eval x)) :
    1 ≤ (det3 U V i j k).rootMultiplicity x := by
  apply (Polynomial.le_rootMultiplicity_iff hdet).mpr
  rw [pow_one]
  apply Polynomial.dvd_iff_isRoot.mpr
  unfold Polynomial.IsRoot det3
  simp only [eval_sub, eval_mul]
  rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rw [hu, hv] <;> ring

omit [DecidableEq F] in
private theorem rootMult_ge_two_of_triple (U V : Fin 4 → F[X]) (i j k : Fin 4)
    (hdet : det3 U V i j k ≠ 0) (x : F)
    (hij : (U i).eval x = (U j).eval x ∧ (V i).eval x = (V j).eval x)
    (hik : (U i).eval x = (U k).eval x ∧ (V i).eval x = (V k).eval x) :
    2 ≤ (det3 U V i j k).rootMultiplicity x := by
  apply (Polynomial.le_rootMultiplicity_iff hdet).mpr
  have d1 : X - C x ∣ U j - U i :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hij.1])
  have d2 : X - C x ∣ V k - V i :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hik.2])
  have d3 : X - C x ∣ U k - U i :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hik.1])
  have d4 : X - C x ∣ V j - V i :=
    Polynomial.dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot, hij.2])
  rw [sq]
  exact dvd_sub (mul_dvd_mul d1 d2) (mul_dvd_mul d3 d4)

/-- Helper for evaluating `distinctAt` by splitting on pairwise equalities of 4 points. -/
private theorem image_fin4_eq {α : Type*} [DecidableEq α] (f : Fin 4 → α) :
    univ.image f = {f 0, f 1, f 2, f 3} := by
  ext y
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- Pointwise inequality in Case A (all four triples non-collinear). -/
private theorem caseA_pointwise (U V : Fin 4 → F[X])
    (h012 : det3 U V 0 1 2 ≠ 0) (h013 : det3 U V 0 1 3 ≠ 0)
    (h023 : det3 U V 0 2 3 ≠ 0) (h123 : det3 U V 1 2 3 ≠ 0) (x : F) :
    2 * meetingExcess U V x ≤
      (det3 U V 0 1 2).rootMultiplicity x + (det3 U V 0 1 3).rootMultiplicity x +
      (det3 U V 0 2 3).rootMultiplicity x + (det3 U V 1 2 3).rootMultiplicity x := by
  let P : Fin 4 → F × F := fun i => ((U i).eval x, (V i).eval x)
  have hpair : ∀ i j, P i = P j ↔ (U i).eval x = (U j).eval x ∧ (V i).eval x = (V j).eval x :=
    fun _ _ => Prod.ext_iff
  have m1_012 := rootMult_ge_one_of_eq U V 0 1 2 h012 x
  have m1_013 := rootMult_ge_one_of_eq U V 0 1 3 h013 x
  have m1_023 := rootMult_ge_one_of_eq U V 0 2 3 h023 x
  have m1_123 := rootMult_ge_one_of_eq U V 1 2 3 h123 x
  have m2_012 := rootMult_ge_two_of_triple U V 0 1 2 h012 x
  have m2_013 := rootMult_ge_two_of_triple U V 0 1 3 h013 x
  have m2_023 := rootMult_ge_two_of_triple U V 0 2 3 h023 x
  have m2_123 := rootMult_ge_two_of_triple U V 1 2 3 h123 x
  have hex : meetingExcess U V x = 4 - ({P 0, P 1, P 2, P 3} : Finset (F × F)).card := by
    unfold meetingExcess distinctAt
    rw [image_fin4_eq P]
  rw [hex]
  by_cases h01 : P 0 = P 1 <;> by_cases h02 : P 0 = P 2 <;> by_cases h03 : P 0 = P 3
  · have c1 : ({P 0, P 1, P 2, P 3} : Finset _).card = 1 := by
      rw [← h01, ← h02, ← h03]; simp
    rw [c1]
    have a := m2_012 ((hpair 0 1).mp h01) ((hpair 0 2).mp h02)
    have b := m2_013 ((hpair 0 1).mp h01) ((hpair 0 3).mp h03)
    have c := m2_023 ((hpair 0 2).mp h02) ((hpair 0 3).mp h03)
    have d := m2_123 ((hpair 1 2).mp (h01.symm.trans h02)) ((hpair 1 3).mp (h01.symm.trans h03))
    omega
  · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
      rw [← h01, ← h02]; simp [Finset.card_insert_of_notMem, h03]
    rw [c2]
    have a := m2_012 ((hpair 0 1).mp h01) ((hpair 0 2).mp h02)
    have b := m1_013 (Or.inl ((hpair 0 1).mp h01))
    have c := m1_023 (Or.inl ((hpair 0 2).mp h02))
    have d := m1_123 (Or.inl ((hpair 1 2).mp (h01.symm.trans h02)))
    omega
  · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
      rw [← h01, ← h03]; simp [Finset.card_insert_of_notMem, h02, Ne.symm h02]
    rw [c2]
    have a := m1_012 (Or.inl ((hpair 0 1).mp h01))
    have b := m2_013 ((hpair 0 1).mp h01) ((hpair 0 3).mp h03)
    have c := m1_023 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
    have d := m1_123 (Or.inr (Or.inl ((hpair 1 3).mp (h01.symm.trans h03))))
    omega
  · by_cases h23 : P 2 = P 3
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h01, ← h23]; simp [Finset.card_insert_of_notMem, h02]
      rw [c2]
      have a := m1_012 (Or.inl ((hpair 0 1).mp h01))
      have b := m1_013 (Or.inl ((hpair 0 1).mp h01))
      have c := m1_023 (Or.inr (Or.inr ((hpair 2 3).mp h23)))
      have d := m1_123 (Or.inr (Or.inr ((hpair 2 3).mp h23)))
      omega
    · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
        rw [← h01]; simp [Finset.card_insert_of_notMem, h02, h03, h23]
      rw [c3]
      have a := m1_012 (Or.inl ((hpair 0 1).mp h01))
      have b := m1_013 (Or.inl ((hpair 0 1).mp h01))
      omega
  · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
      rw [← h02, ← h03]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
    rw [c2]
    have a := m1_012 (Or.inr (Or.inl ((hpair 0 2).mp h02)))
    have b := m1_013 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
    have c := m2_023 ((hpair 0 2).mp h02) ((hpair 0 3).mp h03)
    have d := m1_123 (Or.inr (Or.inr ((hpair 2 3).mp (h02.symm.trans h03))))
    omega
  · by_cases h13 : P 1 = P 3
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h02, ← h13]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
      rw [c2]
      have a := m1_012 (Or.inr (Or.inl ((hpair 0 2).mp h02)))
      have b := m1_013 (Or.inr (Or.inr ((hpair 1 3).mp h13)))
      have c := m1_023 (Or.inl ((hpair 0 2).mp h02))
      have d := m1_123 (Or.inr (Or.inl ((hpair 1 3).mp h13)))
      omega
    · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
        rw [← h02]; simp [Finset.card_insert_of_notMem, h01, h03, h13, Ne.symm h01]
      rw [c3]
      have a := m1_012 (Or.inr (Or.inl ((hpair 0 2).mp h02)))
      have c := m1_023 (Or.inl ((hpair 0 2).mp h02))
      omega
  · by_cases h12 : P 1 = P 2
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h03, ← h12]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
      rw [c2]
      have a := m1_012 (Or.inr (Or.inr ((hpair 1 2).mp h12)))
      have b := m1_013 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
      have c := m1_023 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
      have d := m1_123 (Or.inl ((hpair 1 2).mp h12))
      omega
    · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
        rw [← h03]; simp [Finset.card_insert_of_notMem, h01, h02, h12, Ne.symm h01, Ne.symm h02]
      rw [c3]
      have b := m1_013 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
      have c := m1_023 (Or.inr (Or.inl ((hpair 0 3).mp h03)))
      omega
  · by_cases h12 : P 1 = P 2 <;> by_cases h13 : P 1 = P 3
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h12, ← h13]; simp [Finset.card_insert_of_notMem, h01]
      rw [c2]
      have a := m1_012 (Or.inr (Or.inr ((hpair 1 2).mp h12)))
      have b := m1_013 (Or.inr (Or.inr ((hpair 1 3).mp h13)))
      have c := m1_023 (Or.inr (Or.inr ((hpair 2 3).mp (h12.symm.trans h13))))
      have d := m2_123 ((hpair 1 2).mp h12) ((hpair 1 3).mp h13)
      omega
    · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
        rw [← h12]; simp [Finset.card_insert_of_notMem, h01, h03, h13]
      rw [c3]
      have a := m1_012 (Or.inr (Or.inr ((hpair 1 2).mp h12)))
      have d := m1_123 (Or.inl ((hpair 1 2).mp h12))
      omega
    · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
        rw [← h13]; simp [Finset.card_insert_of_notMem, h01, h02, h12, Ne.symm h12]
      rw [c3]
      have b := m1_013 (Or.inr (Or.inr ((hpair 1 3).mp h13)))
      have d := m1_123 (Or.inr (Or.inl ((hpair 1 3).mp h13)))
      omega
    · by_cases h23 : P 2 = P 3
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h23]; simp [Finset.card_insert_of_notMem, h01, h02, h12]
        rw [c3]
        have c := m1_023 (Or.inr (Or.inr ((hpair 2 3).mp h23)))
        have d := m1_123 (Or.inr (Or.inr ((hpair 2 3).mp h23)))
        omega
      · have c4 : ({P 0, P 1, P 2, P 3} : Finset _).card = 4 := by
          simp [Finset.card_insert_of_notMem, h01, h02, h03, h12, h13, h23]
        rw [c4]
        omega

/-- Case B (triple `(0, 1, 2)` is collinear and `3` lies off their line):
the sum of meeting excesses is bounded by `4 * d` via a coprime direction factorization. -/
private theorem caseB_collinear_triple {d : ℕ} (U V : Fin 4 → F[X])
    (hU : ∀ i, (U i).natDegree ≤ d) (hV : ∀ i, (V i).natDegree ≤ d)
    (hdist : ∀ i j : Fin 4, i ≠ j → U i ≠ U j ∨ V i ≠ V j)
    (h012 : det3 U V 0 1 2 = 0) (h013 : det3 U V 0 1 3 ≠ 0) (S : Finset F) :
    ∑ x ∈ S, meetingExcess U V x ≤ 4 * d := by
  let u1 := U 1 - U 0
  let v1 := V 1 - V 0
  let u2 := U 2 - U 0
  let v2 := V 2 - V 0
  let u3 := U 3 - U 0
  let v3 := V 3 - V 0
  have h1ne : u1 ≠ 0 ∨ v1 ≠ 0 := by
    rcases hdist 1 0 (by decide) with h | h
    · exact Or.inl (sub_ne_zero.mpr h)
    · exact Or.inr (sub_ne_zero.mpr h)
  have h2ne : u2 ≠ 0 ∨ v2 ≠ 0 := by
    rcases hdist 2 0 (by decide) with h | h
    · exact Or.inl (sub_ne_zero.mpr h)
    · exact Or.inr (sub_ne_zero.mpr h)
  have h12ne : u2 - u1 ≠ 0 ∨ v2 - v1 ≠ 0 := by
    rcases hdist 2 1 (by decide) with h | h
    · left
      show (U 2 - U 0) - (U 1 - U 0) ≠ 0
      rw [sub_sub_sub_cancel_right]
      exact sub_ne_zero.mpr h
    · right
      show (V 2 - V 0) - (V 1 - V 0) ≠ 0
      rw [sub_sub_sub_cancel_right]
      exact sub_ne_zero.mpr h
  let A : F[X] := EuclideanDomain.gcd u1 v1
  have hAne : A ≠ 0 := by
    intro h0
    rcases h1ne with hu | hv
    · exact hu (zero_dvd_iff.mp (h0 ▸ EuclideanDomain.gcd_dvd_left u1 v1))
    · exact hv (zero_dvd_iff.mp (h0 ▸ EuclideanDomain.gcd_dvd_right u1 v1))
  obtain ⟨Sdir, hSu1⟩ := EuclideanDomain.gcd_dvd_left u1 v1
  obtain ⟨Tdir, hTv1⟩ := EuclideanDomain.gcd_dvd_right u1 v1
  have hbez_raw := EuclideanDomain.gcd_eq_gcd_ab u1 v1
  let p := EuclideanDomain.gcdA u1 v1
  let q := EuclideanDomain.gcdB u1 v1
  have hbez : p * Sdir + q * Tdir = 1 := by
    have hmul : A * (p * Sdir + q * Tdir) = A * 1 := by
      calc A * (p * Sdir + q * Tdir)
          = (A * Sdir) * p + (A * Tdir) * q := by ring
        _ = u1 * p + v1 * q := by rw [← hSu1, ← hTv1]
        _ = A := hbez_raw.symm
        _ = A * 1 := (mul_one A).symm
    exact mul_left_cancel₀ hAne hmul
  have hcol : u2 * Tdir = v2 * Sdir := by
    have hdet0 : u1 * v2 - u2 * v1 = 0 := h012
    have hmul : A * (v2 * Sdir - u2 * Tdir) = 0 := by
      calc A * (v2 * Sdir - u2 * Tdir)
          = (A * Sdir) * v2 - u2 * (A * Tdir) := by ring
        _ = u1 * v2 - u2 * v1 := by rw [← hSu1, ← hTv1]
        _ = 0 := hdet0
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hAne)).symm
  let B : F[X] := p * u2 + q * v2
  have hBu2 : B * Sdir = u2 := by
    calc B * Sdir = p * Sdir * u2 + q * (v2 * Sdir) := by ring
      _ = p * Sdir * u2 + q * (u2 * Tdir) := by rw [hcol]
      _ = (p * Sdir + q * Tdir) * u2 := by ring
      _ = u2 := by rw [hbez, one_mul]
  have hBv2 : B * Tdir = v2 := by
    calc B * Tdir = p * (u2 * Tdir) + q * Tdir * v2 := by ring
      _ = p * (v2 * Sdir) + q * Tdir * v2 := by rw [hcol]
      _ = (p * Sdir + q * Tdir) * v2 := by ring
      _ = v2 := by rw [hbez, one_mul]
  have hBne : B ≠ 0 := by
    intro h0
    rcases h2ne with hu | hv
    · exact hu (by rw [← hBu2, h0, zero_mul])
    · exact hv (by rw [← hBv2, h0, zero_mul])
  let C : F[X] := B - A
  have hCne : C ≠ 0 := by
    intro h0
    have hBA : B = A := sub_eq_zero.mp h0
    rcases h12ne with hu | hv
    · exact hu (by rw [← hBu2, hSu1, hBA]; ring)
    · exact hv (by rw [← hBv2, hTv1, hBA]; ring)
  let δ₃ : F[X] := Sdir * v3 - Tdir * u3
  have hδ₃ne : δ₃ ≠ 0 := by
    intro h0
    apply h013
    change u1 * v3 - u3 * v1 = 0
    have hfac : u1 * v3 - u3 * v1 = A * δ₃ := by
      have h1 : u1 * v3 = (A * Sdir) * v3 := congrArg (· * v3) hSu1
      have h2 : u3 * v1 = u3 * (A * Tdir) := congrArg (u3 * ·) hTv1
      rw [h1, h2]
      dsimp only [δ₃]
      ring
    rw [hfac, h0, mul_zero]
  let m := max Sdir.natDegree Tdir.natDegree
  have hS_or_T : Sdir ≠ 0 ∨ Tdir ≠ 0 := by
    by_contra hboth
    push Not at hboth
    have : (1 : F[X]) = 0 := by rw [← hbez, hboth.1, hboth.2]; ring
    exact one_ne_zero this
  have hdeg_mul : ∀ Q : F[X], Q ≠ 0 → (Q * Sdir).natDegree ≤ d → (Q * Tdir).natDegree ≤ d →
      Q.natDegree + m ≤ d := by
    intro Q hQ hQS hQT
    have hS : Sdir ≠ 0 → Q.natDegree + Sdir.natDegree ≤ d := fun hSn => by
      rwa [← Polynomial.natDegree_mul hQ hSn]
    have hT : Tdir ≠ 0 → Q.natDegree + Tdir.natDegree ≤ d := fun hTn => by
      rwa [← Polynomial.natDegree_mul hQ hTn]
    dsimp only [m]
    by_cases hSn : Sdir = 0
    · have hTn : Tdir ≠ 0 := hS_or_T.resolve_left (not_not.mpr hSn)
      have h0 : Sdir.natDegree = 0 := by rw [hSn, natDegree_zero]
      have := hT hTn
      omega
    · by_cases hTn : Tdir = 0
      · have h0 : Tdir.natDegree = 0 := by rw [hTn, natDegree_zero]
        have := hS hSn
        omega
      · have := hS hSn; have := hT hTn; omega
  have hdegA : A.natDegree + m ≤ d := hdeg_mul A hAne
    (hSu1 ▸ natDegree_sub_le_same (hU 1) (hU 0))
    (hTv1 ▸ natDegree_sub_le_same (hV 1) (hV 0))
  have hdegB : B.natDegree + m ≤ d := hdeg_mul B hBne
    (hBu2.symm ▸ natDegree_sub_le_same (hU 2) (hU 0))
    (hBv2.symm ▸ natDegree_sub_le_same (hV 2) (hV 0))
  have hdegC : C.natDegree + m ≤ d := by
    have : C.natDegree ≤ max B.natDegree A.natDegree := natDegree_sub_le B A
    omega
  have hdegδ : δ₃.natDegree ≤ d + m := by
    have hv3 : v3.natDegree ≤ d := natDegree_sub_le_same (hV 3) (hV 0)
    have hu3 : u3.natDegree ≤ d := natDegree_sub_le_same (hU 3) (hU 0)
    have h1 : (Sdir * v3).natDegree ≤ d + m :=
      natDegree_mul_le.trans (by have : Sdir.natDegree ≤ m := le_max_left _ _; omega)
    have h2 : (Tdir * u3).natDegree ≤ d + m :=
      natDegree_mul_le.trans (by have : Tdir.natDegree ≤ m := le_max_right _ _; omega)
    exact natDegree_sub_le_same h1 h2
  have hpt : ∀ x : F, meetingExcess U V x ≤
      (if A.eval x = 0 then 1 else 0) + (if B.eval x = 0 then 1 else 0) +
      (if C.eval x = 0 then 1 else 0) + (if δ₃.eval x = 0 then 1 else 0) := by
    intro x
    let P : Fin 4 → F × F := fun i => ((U i).eval x, (V i).eval x)
    have hSTx : Sdir.eval x ≠ 0 ∨ Tdir.eval x ≠ 0 := by
      by_contra hboth
      push Not at hboth
      have h1 := congrArg (eval x) hbez
      simp [hboth.1, hboth.2] at h1
    have h01_A : P 0 = P 1 → A.eval x = 0 := by
      intro h
      have hu : u1.eval x = 0 := by dsimp only [u1]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).1.symm
      have hv : v1.eval x = 0 := by dsimp only [v1]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).2.symm
      rcases hSTx with hSx | hTx
      · have : A.eval x * Sdir.eval x = 0 := by rw [← eval_mul, ← hSu1]; exact hu
        exact (mul_eq_zero.mp this).resolve_right hSx
      · have : A.eval x * Tdir.eval x = 0 := by rw [← eval_mul, ← hTv1]; exact hv
        exact (mul_eq_zero.mp this).resolve_right hTx
    have h02_B : P 0 = P 2 → B.eval x = 0 := by
      intro h
      have hu : u2.eval x = 0 := by dsimp only [u2]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).1.symm
      have hv : v2.eval x = 0 := by dsimp only [v2]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).2.symm
      rcases hSTx with hSx | hTx
      · have : B.eval x * Sdir.eval x = 0 := by rw [← eval_mul, hBu2]; exact hu
        exact (mul_eq_zero.mp this).resolve_right hSx
      · have : B.eval x * Tdir.eval x = 0 := by rw [← eval_mul, hBv2]; exact hv
        exact (mul_eq_zero.mp this).resolve_right hTx
    have h12_C : P 1 = P 2 → C.eval x = 0 := by
      intro h
      have hUeq : (U 1).eval x = (U 2).eval x := (Prod.ext_iff.mp h).1
      have hVeq : (V 1).eval x = (V 2).eval x := (Prod.ext_iff.mp h).2
      have hu : (u2 - u1).eval x = 0 := by
        dsimp only [u1, u2]
        rw [eval_sub, eval_sub, eval_sub, hUeq]; ring
      have hv : (v2 - v1).eval x = 0 := by
        dsimp only [v1, v2]
        rw [eval_sub, eval_sub, eval_sub, hVeq]; ring
      rcases hSTx with hSx | hTx
      · have : C.eval x * Sdir.eval x = 0 := by
          have : C * Sdir = u2 - u1 := by dsimp only [C]; rw [sub_mul, hBu2, ← hSu1]
          rw [← eval_mul, this]; exact hu
        exact (mul_eq_zero.mp this).resolve_right hSx
      · have : C.eval x * Tdir.eval x = 0 := by
          have : C * Tdir = v2 - v1 := by dsimp only [C]; rw [sub_mul, hBv2, ← hTv1]
          rw [← eval_mul, this]; exact hv
        exact (mul_eq_zero.mp this).resolve_right hTx
    have h3_δ : P 0 = P 3 ∨ P 1 = P 3 ∨ P 2 = P 3 → δ₃.eval x = 0 := by
      rintro (h | h | h)
      · have hu : u3.eval x = 0 := by dsimp only [u3]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).1.symm
        have hv : v3.eval x = 0 := by dsimp only [v3]; rw [eval_sub, sub_eq_zero]; exact (Prod.ext_iff.mp h).2.symm
        simp [δ₃, hu, hv]
      · have hUeq : (U 1).eval x = (U 3).eval x := (Prod.ext_iff.mp h).1
        have hVeq : (V 1).eval x = (V 3).eval x := (Prod.ext_iff.mp h).2
        have hu : u3.eval x = u1.eval x := by dsimp only [u3, u1]; rw [eval_sub, eval_sub, hUeq]
        have hv : v3.eval x = v1.eval x := by dsimp only [v3, v1]; rw [eval_sub, eval_sub, hVeq]
        have h1 : u1.eval x = A.eval x * Sdir.eval x := by rw [hSu1, eval_mul]
        have h2 : v1.eval x = A.eval x * Tdir.eval x := by rw [hTv1, eval_mul]
        simp only [δ₃, eval_sub, eval_mul, hu, hv, h1, h2]; ring
      · have hUeq : (U 2).eval x = (U 3).eval x := (Prod.ext_iff.mp h).1
        have hVeq : (V 2).eval x = (V 3).eval x := (Prod.ext_iff.mp h).2
        have hu : u3.eval x = u2.eval x := by dsimp only [u3, u2]; rw [eval_sub, eval_sub, hUeq]
        have hv : v3.eval x = v2.eval x := by dsimp only [v3, v2]; rw [eval_sub, eval_sub, hVeq]
        have h1 : u2.eval x = B.eval x * Sdir.eval x := by rw [← hBu2, eval_mul]
        have h2 : v2.eval x = B.eval x * Tdir.eval x := by rw [← hBv2, eval_mul]
        simp only [δ₃, eval_sub, eval_mul, hu, hv, h1, h2]; ring
    have hex : meetingExcess U V x = 4 - ({P 0, P 1, P 2, P 3} : Finset (F × F)).card := by
      unfold meetingExcess distinctAt; rw [image_fin4_eq P]
    rw [hex]
    by_cases h01 : P 0 = P 1 <;> by_cases h02 : P 0 = P 2 <;> by_cases h03 : P 0 = P 3
    · have c1 : ({P 0, P 1, P 2, P 3} : Finset _).card = 1 := by rw [← h01, ← h02, ← h03]; simp
      have iA : (if A.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h01_A h01)
      have iB : (if B.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h02_B h02)
      have iC : (if C.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h12_C (h01.symm.trans h02))
      have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inl h03))
      omega
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h01, ← h02]; simp [Finset.card_insert_of_notMem, h03]
      have iA : (if A.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h01_A h01)
      have iB : (if B.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h02_B h02)
      omega
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h01, ← h03]; simp [Finset.card_insert_of_notMem, h02, Ne.symm h02]
      have iA : (if A.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h01_A h01)
      have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inl h03))
      omega
    · by_cases h23 : P 2 = P 3
      · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
          rw [← h01, ← h23]; simp [Finset.card_insert_of_notMem, h02]
        have iA : (if A.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h01_A h01)
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inr (Or.inr h23)))
        omega
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h01]; simp [Finset.card_insert_of_notMem, h02, h03, h23]
        have iA : (if A.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h01_A h01)
        omega
    · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
        rw [← h02, ← h03]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
      have iB : (if B.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h02_B h02)
      have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inl h03))
      omega
    · by_cases h13 : P 1 = P 3
      · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
          rw [← h02, ← h13]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
        have iB : (if B.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h02_B h02)
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inr (Or.inl h13)))
        omega
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h02]; simp [Finset.card_insert_of_notMem, h01, h03, h13, Ne.symm h01]
        have iB : (if B.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h02_B h02)
        omega
    · by_cases h12 : P 1 = P 2
      · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
          rw [← h03, ← h12]; simp [Finset.card_insert_of_notMem, h01, Ne.symm h01]
        have iC : (if C.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h12_C h12)
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inl h03))
        omega
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h03]; simp [Finset.card_insert_of_notMem, h01, h02, h12, Ne.symm h01, Ne.symm h02]
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inl h03))
        omega
    · by_cases h12 : P 1 = P 2 <;> by_cases h13 : P 1 = P 3
      · have c2 : ({P 0, P 1, P 2, P 3} : Finset _).card = 2 := by
          rw [← h12, ← h13]; simp [Finset.card_insert_of_notMem, h01]
        have iC : (if C.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h12_C h12)
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inr (Or.inl h13)))
        omega
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h12]; simp [Finset.card_insert_of_notMem, h01, h03, h13]
        have iC : (if C.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h12_C h12)
        omega
      · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
          rw [← h13]; simp [Finset.card_insert_of_notMem, h01, h02, h12, Ne.symm h12]
        have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inr (Or.inl h13)))
        omega
      · by_cases h23 : P 2 = P 3
        · have c3 : ({P 0, P 1, P 2, P 3} : Finset _).card = 3 := by
            rw [← h23]; simp [Finset.card_insert_of_notMem, h01, h02, h12]
          have iD : (if δ₃.eval x = 0 then 1 else 0) = 1 := ite_eq_left (h3_δ (Or.inr (Or.inr h23)))
          omega
        · have c4 : ({P 0, P 1, P 2, P 3} : Finset _).card = 4 := by
            simp [Finset.card_insert_of_notMem, h01, h02, h03, h12, h13, h23]
          omega
  have hsum := Finset.sum_le_sum (s := S) fun x _ => hpt x
  simp only [Finset.sum_add_distrib] at hsum
  have hA := sum_eval_zero_le_natDegree A hAne S
  have hB := sum_eval_zero_le_natDegree B hBne S
  have hC := sum_eval_zero_le_natDegree C hCne S
  have hδ := sum_eval_zero_le_natDegree δ₃ hδ₃ne S
  omega

omit [DecidableEq F] in
private theorem all_det3_zero_of_two_collinear (U V : Fin 4 → F[X])
    (h01 : U 0 ≠ U 1 ∨ V 0 ≠ V 1) (h012 : det3 U V 0 1 2 = 0) (h013 : det3 U V 0 1 3 = 0) :
    ∀ i j k : Fin 4, det3 U V i j k = 0 := by
  have h023 : det3 U V 0 2 3 = 0 := by
    have hu : (U 1 - U 0) * det3 U V 0 2 3 = 0 := by
      have : (U 1 - U 0) * det3 U V 0 2 3 =
          (U 2 - U 0) * det3 U V 0 1 3 - (U 3 - U 0) * det3 U V 0 1 2 := by unfold det3; ring
      rw [this, h013, h012]; ring
    have hv : (V 1 - V 0) * det3 U V 0 2 3 = 0 := by
      have : (V 1 - V 0) * det3 U V 0 2 3 =
          (V 2 - V 0) * det3 U V 0 1 3 - (V 3 - V 0) * det3 U V 0 1 2 := by unfold det3; ring
      rw [this, h013, h012]; ring
    rcases h01 with h | h
    · exact (mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr h.symm)
    · exact (mul_eq_zero.mp hv).resolve_left (sub_ne_zero.mpr h.symm)
  have h123 : det3 U V 1 2 3 = 0 := by
    have : det3 U V 1 2 3 = det3 U V 0 2 3 - det3 U V 0 1 3 + det3 U V 0 1 2 := by unfold det3; ring
    rw [this, h023, h013, h012]; ring
  have hswap12 : ∀ a b c, det3 U V a b c = 0 → det3 U V b a c = 0 := by
    intro a b c h; have : det3 U V b a c = -det3 U V a b c := by unfold det3; ring
    rw [this, h, neg_zero]
  have hswap23 : ∀ a b c, det3 U V a b c = 0 → det3 U V a c b = 0 := by
    intro a b c h; have : det3 U V a c b = -det3 U V a b c := by unfold det3; ring
    rw [this, h, neg_zero]
  have hself : ∀ a b c, (a = b ∨ a = c ∨ b = c) → det3 U V a b c = 0 := by
    rintro a b c (rfl | rfl | rfl) <;> (unfold det3; ring)
  have hord : ∀ a b c : Fin 4, a < b → b < c → det3 U V a b c = 0 := by
    intro a b c hab hbc
    have hcases : (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 1 ∧ c = 3) ∨
        (a = 0 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ b = 2 ∧ c = 3) := by
      omega
    rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact h012
    · exact h013
    · exact h023
    · exact h123
  intro i j k
  by_cases hdup : i = j ∨ i = k ∨ j = k
  · exact hself i j k hdup
  · push Not at hdup
    obtain ⟨hij, hik, hjk⟩ := hdup
    rcases lt_or_gt_of_ne hij with h1 | h1
    · rcases lt_or_gt_of_ne hjk with h2 | h2
      · exact hord i j k h1 h2
      · rcases lt_or_gt_of_ne hik with h3 | h3
        · exact hswap23 i k j (hord i k j h3 h2)
        · exact hswap23 i k j (hswap12 k i j (hord k i j h3 h1))
    · rcases lt_or_gt_of_ne hik with h2 | h2
      · exact hswap12 j i k (hord j i k h1 h2)
      · rcases lt_or_gt_of_ne hjk with h3 | h3
        · exact hswap12 j i k (hswap23 j k i (hord j k i h3 h2))
        · exact hswap12 j i k (hswap23 j k i (hswap12 k j i (hord k j i h3 h1)))

/-- **Universal `4 * d` Meeting-Excess Theorem (any field, any characteristic, any degree `d`):**
For any four pairwise-distinct non-collinear polynomial pairs `(U_i, V_i) ∈ F[X]_{≤ d}^2` and
any finite set `S ⊆ F`, the total meeting excess satisfies `∑ x ∈ S, (4 - distinctAt x) ≤ 4 * d`. -/
theorem four_noncollinear_meeting_excess_le {d : ℕ} (U V : Fin 4 → F[X])
    (hU : ∀ i, (U i).natDegree ≤ d) (hV : ∀ i, (V i).natDegree ≤ d)
    (hdist : ∀ i j : Fin 4, i ≠ j → U i ≠ U j ∨ V i ≠ V j)
    (hnoncol : ∃ i j k : Fin 4, det3 U V i j k ≠ 0) (S : Finset F) :
    ∑ x ∈ S, meetingExcess U V x ≤ 4 * d := by
  by_cases h012 : det3 U V 0 1 2 = 0
  · have h013 : det3 U V 0 1 3 ≠ 0 := by
      intro h0
      obtain ⟨i, j, k, hne⟩ := hnoncol
      exact hne (all_det3_zero_of_two_collinear U V (hdist 0 1 (by decide)) h012 h0 i j k)
    exact caseB_collinear_triple U V hU hV hdist h012 h013 S
  · by_cases h013 : det3 U V 0 1 3 = 0
    · let σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
      have hperm_eq : ∑ x ∈ S, meetingExcess U V x = ∑ x ∈ S, meetingExcess (U ∘ σ) (V ∘ σ) x :=
        Finset.sum_congr rfl fun x _ => (meetingExcess_perm U V σ x).symm
      rw [hperm_eq]
      have hs0 : σ 0 = 0 := by decide
      have hs1 : σ 1 = 1 := by decide
      have hs2 : σ 2 = 3 := by decide
      have hs3 : σ 3 = 2 := by decide
      exact caseB_collinear_triple (U ∘ σ) (V ∘ σ) (fun i => hU (σ i)) (fun i => hV (σ i))
        (fun i j hne => hdist (σ i) (σ j) (σ.injective.ne hne))
        (by unfold det3 at h013 ⊢; simp only [Function.comp_apply, hs0, hs1, hs2]; exact h013)
        (by unfold det3 at h012 ⊢; simp only [Function.comp_apply, hs0, hs1, hs3]; exact h012) S
    · by_cases h023 : det3 U V 0 2 3 = 0
      · let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 3
        have hperm_eq : ∑ x ∈ S, meetingExcess U V x = ∑ x ∈ S, meetingExcess (U ∘ σ) (V ∘ σ) x :=
          Finset.sum_congr rfl fun x _ => (meetingExcess_perm U V σ x).symm
        rw [hperm_eq]
        have hs0 : σ 0 = 0 := by decide
        have hs1 : σ 1 = 3 := by decide
        have hs2 : σ 2 = 2 := by decide
        have hs3 : σ 3 = 1 := by decide
        have hcol' : det3 (U ∘ σ) (V ∘ σ) 0 1 2 = 0 := by
          have : det3 (U ∘ σ) (V ∘ σ) 0 1 2 = -det3 U V 0 2 3 := by
            unfold det3; simp only [Function.comp_apply, hs0, hs1, hs2]; ring
          rw [this, h023, neg_zero]
        have hne' : det3 (U ∘ σ) (V ∘ σ) 0 1 3 ≠ 0 := by
          have : det3 (U ∘ σ) (V ∘ σ) 0 1 3 = -det3 U V 0 1 3 := by
            unfold det3; simp only [Function.comp_apply, hs0, hs1, hs3]; ring
          rw [this]; exact neg_ne_zero.mpr h013
        exact caseB_collinear_triple (U ∘ σ) (V ∘ σ) (fun i => hU (σ i)) (fun i => hV (σ i))
          (fun i j hne => hdist (σ i) (σ j) (σ.injective.ne hne)) hcol' hne' S
      · by_cases h123 : det3 U V 1 2 3 = 0
        · let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 3
          have hperm_eq : ∑ x ∈ S, meetingExcess U V x = ∑ x ∈ S, meetingExcess (U ∘ σ) (V ∘ σ) x :=
            Finset.sum_congr rfl fun x _ => (meetingExcess_perm U V σ x).symm
          rw [hperm_eq]
          have hs0 : σ 0 = 3 := by decide
          have hs1 : σ 1 = 1 := by decide
          have hs2 : σ 2 = 2 := by decide
          have hs3 : σ 3 = 0 := by decide
          have hcol' : det3 (U ∘ σ) (V ∘ σ) 0 1 2 = 0 := by
            have : det3 (U ∘ σ) (V ∘ σ) 0 1 2 = det3 U V 1 2 3 := by
              unfold det3; simp only [Function.comp_apply, hs0, hs1, hs2]; ring
            rw [this, h123]
          have hne' : det3 (U ∘ σ) (V ∘ σ) 0 1 3 ≠ 0 := by
            have : det3 (U ∘ σ) (V ∘ σ) 0 1 3 = -det3 U V 0 1 3 := by
              unfold det3; simp only [Function.comp_apply, hs0, hs1, hs3]; ring
            rw [this]; exact neg_ne_zero.mpr h013
          exact caseB_collinear_triple (U ∘ σ) (V ∘ σ) (fun i => hU (σ i)) (fun i => hV (σ i))
            (fun i j hne => hdist (σ i) (σ j) (σ.injective.ne hne)) hcol' hne' S
        · have hsum := Finset.sum_le_sum (s := S) fun x _ =>
            caseA_pointwise U V h012 h013 h023 h123 x
          rw [← Finset.mul_sum] at hsum
          simp only [Finset.sum_add_distrib] at hsum
          have r1 := (sum_rootMultiplicity_le_natDegree _ h012 S).trans (natDegree_det3_le U V hU hV 0 1 2)
          have r2 := (sum_rootMultiplicity_le_natDegree _ h013 S).trans (natDegree_det3_le U V hU hV 0 1 3)
          have r3 := (sum_rootMultiplicity_le_natDegree _ h023 S).trans (natDegree_det3_le U V hU hV 0 2 3)
          have r4 := (sum_rootMultiplicity_le_natDegree _ h123 S).trans (natDegree_det3_le U V hU hV 1 2 3)
          omega

/-- Sharpness of `SecondPrimePlanarQuartet.lean` (`553,648,129`) and `EighthTransverseAttack.lean`
(`679,477,248`): four distinct non-collinear cubics over any field have total meeting excess ≤ 12. -/
theorem four_noncollinear_cubics_le_twelve (U V : Fin 4 → F[X])
    (hU : ∀ i, (U i).natDegree ≤ 3) (hV : ∀ i, (V i).natDegree ≤ 3)
    (hdist : ∀ i j : Fin 4, i ≠ j → U i ≠ U j ∨ V i ≠ V j)
    (hnoncol : ∃ i j k : Fin 4, det3 U V i j k ≠ 0) (S : Finset F) :
    ∑ x ∈ S, meetingExcess U V x ≤ 12 :=
  four_noncollinear_meeting_excess_le U V hU hV hdist hnoncol S

/-- Saturation ceiling for four distinct non-collinear septics over any field: excess ≤ 28. -/
theorem four_noncollinear_septics_le_28 (U V : Fin 4 → F[X])
    (hU : ∀ i, (U i).natDegree ≤ 7) (hV : ∀ i, (V i).natDegree ≤ 7)
    (hdist : ∀ i j : Fin 4, i ≠ j → U i ≠ U j ∨ V i ≠ V j)
    (hnoncol : ∃ i j k : Fin 4, det3 U V i j k ≠ 0) (S : Finset F) :
    ∑ x ∈ S, meetingExcess U V x ≤ 28 :=
  four_noncollinear_meeting_excess_le U V hU hV hdist hnoncol S

end FourNoncollinear

/-! ## Part 2: Universal quotient-free label-core conservation and `H`-count barriers -/

section QuotientFreeBarriers

/-- Universal label-core conservation: if `H` cores each have size ≥ `c` inside a domain
of size `n` and supply at most `∑ i, (C i)ᶜ.card` total 1-fresh labels `L`, then
`H * c + L ≤ H * n`. -/
theorem label_core_conservation {I : Type*} [Fintype I] [DecidableEq I] {H n c L : ℕ}
    (C : Fin H → Finset I) (hI : Fintype.card I = n)
    (hC : ∀ i, c ≤ (C i).card) (hL : L ≤ ∑ i : Fin H, (C i)ᶜ.card) :
    H * c + L ≤ H * n := by
  have hsum : ∑ i : Fin H, ((C i).card + (C i)ᶜ.card) = H * n := by
    have heach : ∀ i : Fin H, (C i).card + (C i)ᶜ.card = n := fun i => by
      rw [card_add_card_compl, hI]
    simp [heach]
  rw [Finset.sum_add_distrib] at hsum
  have hlow : H * c ≤ ∑ i : Fin H, (C i).card := by
    calc H * c = ∑ _i : Fin H, c := by simp
      _ ≤ ∑ i : Fin H, (C i).card := Finset.sum_le_sum fun i _ => hC i
  omega

private theorem sum_deg_eq {I : Type*} [Fintype I] [DecidableEq I] {H : ℕ}
    (Cov : Finset I) (C : Fin H → Finset I) (hsub : ∀ i, C i ⊆ Cov) :
    ∑ x ∈ Cov, (univ.filter fun i : Fin H => x ∈ C i).card = ∑ i : Fin H, (C i).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_filter, filter_mem_eq_inter, Finset.inter_eq_right.mpr (hsub i)]

private theorem sum_deg_pairs_eq {I : Type*} [Fintype I] [DecidableEq I] {H : ℕ}
    (Cov : Finset I) (C : Fin H → Finset I) (hsub : ∀ i, C i ⊆ Cov) :
    ∑ x ∈ Cov, (univ.filter fun i : Fin H => x ∈ C i).card *
      ((univ.filter fun i : Fin H => x ∈ C i).card - 1) =
    ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
  have hpair_x : ∀ x : I,
      (univ.filter fun i : Fin H => x ∈ C i).card *
        ((univ.filter fun i : Fin H => x ∈ C i).card - 1) =
      ∑ i : Fin H, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 := by
    intro x
    let Sx : Finset (Fin H) := univ.filter fun i => x ∈ C i
    have hsum_off : Sx.card * (Sx.card - 1) = ∑ i ∈ Sx, ∑ _j ∈ Sx.erase i, (1 : ℕ) := by
      have hinner_card : ∀ i ∈ Sx, ∑ _j ∈ Sx.erase i, (1 : ℕ) = Sx.card - 1 := fun i hi => by
        rw [Finset.sum_const, Finset.card_erase_of_mem hi, smul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl hinner_card, Finset.sum_const, smul_eq_mul]
    rw [hsum_off]
    have hinner : ∀ i : Fin H,
        (if x ∈ C i then ∑ j ∈ Sx.erase i, (1 : ℕ) else 0) =
        ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 := by
      intro i
      by_cases hi : x ∈ C i
      · simp only [hi, ↓reduceIte, mem_inter, true_and]
        rw [← sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j; simp [Sx]
      · simp only [hi, ↓reduceIte, mem_inter, false_and, sum_const_zero]
    calc ∑ i ∈ Sx, ∑ j ∈ Sx.erase i, (1 : ℕ)
        = ∑ i : Fin H, if x ∈ C i then ∑ j ∈ Sx.erase i, (1 : ℕ) else 0 := by rw [← sum_filter]
      _ = ∑ i : Fin H, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_congr rfl fun i _ => hinner i
  calc ∑ x ∈ Cov, (univ.filter fun i : Fin H => x ∈ C i).card *
        ((univ.filter fun i : Fin H => x ∈ C i).card - 1)
      = ∑ x ∈ Cov, ∑ i : Fin H, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
          Finset.sum_congr rfl fun x _ => hpair_x x
    _ = ∑ i : Fin H, ∑ x ∈ Cov, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
          Finset.sum_comm
    _ = ∑ i : Fin H, ∑ j ∈ univ.erase i, ∑ x ∈ Cov, if x ∈ C i ∩ C j then 1 else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [← sum_filter, filter_mem_eq_inter,
            Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans (hsub i)), card_eq_sum_ones]

/-- Discrete pairwise-degree Johnson hull on any subset `Cov ⊆ univ` containing all cores
`C i ⊆ Cov`: for every integer `a`, `2 * a * H * c ≤ H * (H - 1) * d + a * (a + 1) * Cov.card`. -/
theorem discrete_johnson_hull {I : Type*} [Fintype I] [DecidableEq I] {H d c : ℕ}
    (Cov : Finset I) (C : Fin H → Finset I)
    (hsub : ∀ i, C i ⊆ Cov) (hC : ∀ i, c ≤ (C i).card)
    (hover : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ d) (a : ℕ) :
    2 * a * H * c ≤ H * (H - 1) * d + a * (a + 1) * Cov.card := by
  let deg (x : I) : ℕ := (univ.filter fun i : Fin H => x ∈ C i).card
  have hpt : ∀ x : I, 2 * a * deg x ≤ deg x * (deg x - 1) + a * (a + 1) := by
    intro x
    have hsq : 0 ≤ ((deg x : ℤ) - (a : ℤ)) * ((deg x : ℤ) - (a : ℤ) - 1) := by
      rcases le_or_gt (deg x) a with hle | hgt
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    have h1 : deg x * (deg x - 1) + deg x = deg x * deg x := by
      cases deg x with
      | zero => simp
      | succ k => simp; ring
    have hz : ((2 * a * deg x : ℕ) : ℤ) ≤ ((deg x * (deg x - 1) + a * (a + 1) : ℕ) : ℤ) := by
      have h1z : ((deg x * (deg x - 1) : ℕ) : ℤ) + (deg x : ℤ) = (deg x : ℤ) * (deg x : ℤ) := by
        exact_mod_cast h1
      push_cast [Nat.cast_add, Nat.cast_mul]
      nlinarith
    exact Int.ofNat_le.mp hz
  have hub : ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card ≤ H * (H - 1) * d := by
    calc ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card
        ≤ ∑ i : Fin H, ∑ _j ∈ univ.erase i, d :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
              hover i j (mem_erase.mp hj).1.symm
      _ = H * (H - 1) * d := by
            simp [Finset.sum_const, Finset.card_erase_of_mem, mul_assoc]
  have hlow : H * c ≤ ∑ i : Fin H, (C i).card := by
    calc H * c = ∑ _i : Fin H, c := by simp
      _ ≤ ∑ i : Fin H, (C i).card := Finset.sum_le_sum fun i _ => hC i
  have hs := Finset.sum_le_sum (s := Cov) fun x _ => hpt x
  rw [← Finset.mul_sum, sum_deg_eq Cov C hsub, Finset.sum_add_distrib,
    sum_deg_pairs_eq Cov C hsub, Finset.sum_const, smul_eq_mul, mul_comm Cov.card] at hs
  have h2a := Nat.mul_le_mul_left (2 * a) hlow
  rw [← mul_assoc] at h2a
  omega

/-- Continuous Cauchy–Schwarz Johnson hull on a covering set `Cov`:
`(H * c)^2 ≤ Cov.card * (H * c + H * (H - 1) * d)`. -/
theorem continuous_johnson_hull {I : Type*} [Fintype I] [DecidableEq I] {H d c : ℕ}
    (Cov : Finset I) (C : Fin H → Finset I)
    (hsub : ∀ i, C i ⊆ Cov) (hC : ∀ i, c ≤ (C i).card)
    (hover : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ d) :
    (H * c) ^ 2 ≤ Cov.card * (H * c + H * (H - 1) * d) := by
  let deg (x : I) : ℕ := (univ.filter fun i : Fin H => x ∈ C i).card
  have hsum_deg : ∑ x ∈ Cov, deg x = ∑ i : Fin H, (C i).card := sum_deg_eq Cov C hsub
  have hsum_sq : ∑ x ∈ Cov, deg x ^ 2 =
      (∑ i : Fin H, (C i).card) + ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
    have hsplit : ∀ x : I, deg x ^ 2 = deg x + deg x * (deg x - 1) := by
      intro x
      cases deg x with
      | zero => simp
      | succ k => simp [sq]; ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, hsum_deg]
    congr 1
    exact sum_deg_pairs_eq Cov C hsub
  have hcs : (∑ x ∈ Cov, deg x) ^ 2 ≤ Cov.card * ∑ x ∈ Cov, deg x ^ 2 := by
    have hnn : (0 : ℤ) ≤ ∑ x ∈ Cov, ∑ y ∈ Cov, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ∑ x ∈ Cov, ∑ y ∈ Cov, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 =
        2 * (Cov.card : ℤ) * (∑ x ∈ Cov, (deg x : ℤ) ^ 2) - 2 * (∑ x ∈ Cov, (deg x : ℤ)) ^ 2 := by
      have hterm : ∀ x y, ((deg x : ℤ) - (deg y : ℤ)) ^ 2 =
          (deg x : ℤ) ^ 2 - 2 * ((deg x : ℤ) * (deg y : ℤ)) + (deg y : ℤ) ^ 2 := fun _ _ => by ring
      simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h1 : ∑ x ∈ Cov, ∑ _y ∈ Cov, (deg x : ℤ) ^ 2 =
          (Cov.card : ℤ) * ∑ x ∈ Cov, (deg x : ℤ) ^ 2 := by
        simp [Finset.sum_const, Finset.mul_sum]
      have h2 : ∑ _x ∈ Cov, ∑ y ∈ Cov, (deg y : ℤ) ^ 2 =
          (Cov.card : ℤ) * ∑ y ∈ Cov, (deg y : ℤ) ^ 2 := by
        simp [Finset.sum_const]
      have h3 : ∑ x ∈ Cov, ∑ y ∈ Cov, 2 * ((deg x : ℤ) * (deg y : ℤ)) =
          2 * (∑ x ∈ Cov, (deg x : ℤ)) ^ 2 := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring
      rw [h1, h2, h3]; ring
    have hz : (∑ x ∈ Cov, (deg x : ℤ)) ^ 2 ≤ (Cov.card : ℤ) * ∑ x ∈ Cov, (deg x : ℤ) ^ 2 := by
      linarith
    exact_mod_cast hz
  set Ssum := ∑ i : Fin H, (C i).card
  have hSge : H * c ≤ Ssum := by
    calc H * c = ∑ _i : Fin H, c := by simp
      _ ≤ Ssum := Finset.sum_le_sum fun i _ => hC i
  have hub : ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card ≤ H * (H - 1) * d := by
    calc ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card
        ≤ ∑ i : Fin H, ∑ _j ∈ univ.erase i, d :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
              hover i j (mem_erase.mp hj).1.symm
      _ = H * (H - 1) * d := by
            simp [Finset.sum_const, Finset.card_erase_of_mem, mul_assoc]
  rw [hsum_deg, hsum_sq] at hcs
  have h1 : Ssum ^ 2 ≤ Cov.card * (Ssum + H * (H - 1) * d) :=
    hcs.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hub Ssum))
  rcases le_or_gt (H * c) Cov.card with hsmall | hbig
  · calc (H * c) ^ 2 = (H * c) * (H * c) := sq _
      _ ≤ Cov.card * (H * c) := Nat.mul_le_mul_right _ hsmall
      _ ≤ Cov.card * (H * c + H * (H - 1) * d) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  · nlinarith

/-- **Production `p2` label-core conservation barriers (`N = 2^30`, `B_2 = 2^31`):**
Any 1-fresh witness exceeding `B_2 = 2^31` bad scalars with `H` heads and `e = N - (c + 1)`
satisfies:
- `H ≤ 4 → 536,870,912 ≤ e` (`1/2 n`),
- `H = 5 → 429,496,729 ≤ e`,
- `H = 6 → 357,913,941 ≤ e` (so beating `357,913,941` unconditionally requires `H ≥ 7`). -/
theorem p2_head_count_barriers {H c e L : ℕ}
    (hcons : H * c + L ≤ H * 1073741824) (hB : 2147483648 < L) (he : e + c + 1 = 1073741824) :
    (H ≤ 4 → 536870912 ≤ e) ∧
    (H = 5 → 429496729 ≤ e) ∧
    (H = 6 → 357913941 ≤ e) := by
  refine ⟨fun h4 => ?_, fun h5 => ?_, fun h6 => ?_⟩
  · interval_cases H <;> omega
  · subst h5; omega
  · subst h6; omega

/-- **First-prime quarter-rate (`d = 2^28 - 1`, `N = 2^30`) `H ≥ 5` exclusion:**
Every 1-fresh witness (2D planar OR 1D collinear, zero quotient assumptions!) with `H ≥ 5`
heads of degree `≤ 2^28 - 1` is unconditionally forced to `e ≥ 483,183,821 > 480,946,859`. -/
theorem p1_quarter_five_plus_barrier {I : Type*} [Fintype I] [DecidableEq I] {H c e : ℕ}
    (C : Fin H → Finset I) (hI : Fintype.card I = 1073741824)
    (hH : 5 ≤ H) (hC : ∀ i, c ≤ (C i).card)
    (hover : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ 268435455)
    (he : e + c + 1 = 1073741824) :
    483183821 ≤ e := by
  by_cases h5 : H = 5
  · subst h5
    have hdisc := discrete_johnson_hull (univ : Finset I) C (fun _ => subset_univ _) hC hover 2
    rw [Finset.card_univ, hI] at hdisc
    omega
  · have h6 : 6 ≤ H := by omega
    have hcs := continuous_johnson_hull (univ : Finset I) C (fun _ => subset_univ _) hC hover
    rw [Finset.card_univ, hI] at hcs
    by_contra hlt
    have hc : 590558003 ≤ c := by omega
    have hpos : 0 < H := by omega
    have hdiv : H * c ^ 2 ≤ 1073741824 * (c + (H - 1) * 268435455) := by
      have hmul : H * (H * c ^ 2) ≤ H * (1073741824 * (c + (H - 1) * 268435455)) := by
        calc H * (H * c ^ 2) = (H * c) ^ 2 := by ring
          _ ≤ 1073741824 * (H * c + H * (H - 1) * 268435455) := hcs
          _ = H * (1073741824 * (c + (H - 1) * 268435455)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul hpos
    -- Shift to nonnegative coordinates k = H - 6, u = c - 590558003: LHS > RHS with all positive terms!
    let k := H - 6
    let u := c - 590558003
    have hHk : H = k + 6 := by omega
    have hH1 : H - 1 = k + 5 := by omega
    have hcu : c = u + 590558003 := by omega
    rw [hH1, hHk, hcu] at hdiv
    have hexact :
        (k + 6) * (u + 590558003) ^ 2 =
        1073741824 * (u + 590558003 + (k + 5) * 268435455) +
          (17293826735220982 + 60528379829378089 * k + 6012954212 * u +
            1181116006 * k * u + 6 * u ^ 2 + k * u ^ 2) := by ring
    omega

/-- **Second-prime eighth-rate (`d = 2^27 - 1`, `N = 2^30`, `B_2 = 2^31`) 1D collinear barrier:**
Every 1D collinear 1-fresh witness of **any** head count `H ≥ 2` (with `Cov` the union of the
`H` cores, `p0 = N - Cov.card` uncovered sites supplying `H` labels each, and covered sites
supplying `1` label each, so `Cov.card + H * (N - Cov.card) > 2^31`) is unconditionally forced
to `e ≥ 683,871,281 > 679,477,248`. Hence any beat below `679,477,248` MUST be non-collinear. -/
theorem p2_eighth_collinear_barrier {I : Type*} [Fintype I] [DecidableEq I] {H c e : ℕ}
    (Cov : Finset I) (C : Fin H → Finset I) (hI : Fintype.card I = 1073741824)
    (hH : 2 ≤ H) (hsub : ∀ i, C i ⊆ Cov) (hC : ∀ i, c ≤ (C i).card)
    (hover : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ 134217727)
    (hcolL : 2147483648 < Cov.card + H * (1073741824 - Cov.card))
    (he : e + c + 1 = 1073741824) :
    683871281 ≤ e := by
  have hcov_le : Cov.card ≤ 1073741824 := by
    calc Cov.card ≤ (univ : Finset I).card := card_le_univ _
      _ = 1073741824 := by rw [card_univ, hI]
  have hcov_bound : (H - 1) * Cov.card + 1073741825 ≤ (H - 1) * 1073741824 := by
    have : Cov.card + H * (1073741824 - Cov.card) =
        1073741824 + (H - 1) * (1073741824 - Cov.card) := by
      cases H with
      | zero => omega
      | succ m =>
        have : m + 1 - 1 = m := by omega
        rw [this, Nat.succ_mul]
        omega
    have hp0 : 1073741825 ≤ (H - 1) * (1073741824 - Cov.card) := by omega
    rw [Nat.mul_sub_left_distrib] at hp0
    have hmul : (H - 1) * Cov.card ≤ (H - 1) * 1073741824 := Nat.mul_le_mul_left _ hcov_le
    omega
  by_cases h12 : H < 12
  · interval_cases H
    · omega
    · have := discrete_johnson_hull Cov C hsub hC hover 1; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 2; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 2; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 2; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 3; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 3; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 3; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 4; omega
    · have := discrete_johnson_hull Cov C hsub hC hover 4; omega
  · have hge12 : 12 ≤ H := by omega
    have hcs := continuous_johnson_hull Cov C hsub hC hover
    by_contra hlt
    have hc : 389870543 ≤ c := by omega
    have hpos : 0 < H := by omega
    have hdiv : H * c ^ 2 ≤ Cov.card * (c + (H - 1) * 134217727) := by
      have hmul : H * (H * c ^ 2) ≤ H * (Cov.card * (c + (H - 1) * 134217727)) := by
        calc H * (H * c ^ 2) = (H * c) ^ 2 := by ring
          _ ≤ Cov.card * (H * c + H * (H - 1) * 134217727) := hcs
          _ = H * (Cov.card * (c + (H - 1) * 134217727)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul hpos
    have hmul1 : (H - 1) * (H * c ^ 2) ≤ ((H - 1) * Cov.card) * (c + (H - 1) * 134217727) := by
      calc (H - 1) * (H * c ^ 2)
          ≤ (H - 1) * (Cov.card * (c + (H - 1) * 134217727)) := Nat.mul_le_mul_left _ hdiv
        _ = ((H - 1) * Cov.card) * (c + (H - 1) * 134217727) := by ring
    let k := H - 12
    let u := c - 389870543
    have hHk : H = k + 12 := by omega
    have hH1 : H - 1 = k + 11 := by omega
    have hcov_hi : (H - 1) * Cov.card ≤ (k + 10) * 1073741824 := by
      rw [hH1] at hcov_bound ⊢
      omega
    have hstep : (H - 1) * (H * c ^ 2) ≤ (k + 10) * 1073741824 * (c + (H - 1) * 134217727) :=
      hmul1.trans (Nat.mul_le_mul_right _ hcov_hi)
    have hcu : c = u + 389870543 := by omega
    rw [hH1, hHk, hcu] at hstep
    have hexact :
        (k + 11) * ((k + 12) * (u + 389870543) ^ 2) =
        (k + 10) * 1073741824 * (u + 389870543 + (k + 11) * 134217727) +
          (24999669603710468 + 50938691870556087 * k + 7883853297000801 * k ^ 2 +
            92188405112 * u + 16860303154 * k * u + 779741086 * k ^ 2 * u +
            132 * u ^ 2 + 23 * k * u ^ 2 + k ^ 2 * u ^ 2) := by ring
    omega

end QuotientFreeBarriers

/-! ## Part 3: Global full-rank 2D optimality of `SecondPrimeCyclicCubics` (`31/48`) -/

section FullRankOptimality

/-- **Universal Full-Rank 2D Planar Core Cap:**
In any full-rank 2D planar arrangement of `H` heads of quotient degree `D` on `M` fibers with
`r` root fibers, `a` owned non-root fibers (`r + a ≤ M`), degree cap `r + D ≤ K` (where
`K = ρ * M`), and full-rank 2D meeting budget `E ≤ (H - 1) * (D + 1) - 2`, the total core
slot count `C_tot = H * r + E + a` satisfies `C_tot + 3 ≤ H * (K + 1) + (M - K)`. -/
theorem full_rank_planar_core_cap {M H D K r a E C_tot : ℕ}
    (hH : 1 ≤ H) (hdeg : r + D ≤ K) (hpart : r + a ≤ M) (hK : K ≤ M)
    (hfull : E + 2 ≤ (H - 1) * (D + 1)) (hC : C_tot ≤ H * r + E + a) :
    C_tot + 3 ≤ H * (K + 1) + (M - K) := by
  let m := H - 1
  have hHm : H = m + 1 := by omega
  have h1 : (m + 1) * r + m * (D + 1) + a ≤ m * K + m + M := by
    have : m * (r + D) ≤ m * K := Nat.mul_le_mul_left m hdeg
    have : (m + 1) * r + m * (D + 1) + a = m * (r + D) + m + (r + a) := by ring
    omega
  have h2 : m * K + m + M + 1 = (m + 1) * (K + 1) + (M - K) := by
    have : (m + 1) * (K + 1) = m * K + m + K + 1 := by ring
    omega
  rw [hHm] at hfull hC ⊢
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub] at hfull
  omega

/-- **Exact Global Full-Rank Optimality of `SecondPrimeCyclicCubics` (`31/48` at `M = 8, H = 6`):**
At half rate (`M = 2 * K`, `4 ≤ K` so `M ≥ 8`), every full-rank 2D planar arrangement of `H ≥ 4`
heads whose total core sum `C_tot = ∑ c_i` satisfies both the `p2` label-conservation requirement
`C_tot + 4 * K < H * (2 * K)` and the full-rank cap `C_tot ≤ H * (K + 1) + K - 3` has average
core fraction `C_tot / (H * 2 * K) ≤ 31 / 48`, with equality **uniquely** at `K = 4, H = 6`
(`M = 8, D = 3, H = 6`, `C_tot = 31`, realized by `SecondPrimeCyclicCubics.lean` at `380,283,564`). -/
theorem second_prime_half_full_rank_optimal {K H C_tot : ℕ}
    (hK : 4 ≤ K) (hH : 4 ≤ H)
    (hfull : C_tot ≤ H * (K + 1) + K - 3)
    (hlabel : C_tot + 4 * K < H * (2 * K)) :
    48 * C_tot ≤ 31 * (H * (2 * K)) ∧
    (48 * C_tot = 31 * (H * (2 * K)) → K = 4 ∧ H = 6) := by
  have hK4 : K = 4 ∨ 5 ≤ K := by omega
  rcases hK4 with rfl | hK5
  · by_cases hH6 : H ≤ 6
    · interval_cases H <;> constructor <;> omega
    · have hfull' : C_tot ≤ 5 * H + 1 := by omega
      constructor <;> omega
  · by_cases hH5 : H ≤ 5
    · interval_cases H <;> constructor <;> omega
    · let k := K - 5
      let h := H - 6
      have hKk : K = k + 5 := by omega
      have hHh : H = h + 6 := by omega
      have hpos : 3 ≤ H * (K + 1) + K := by
        rw [hKk, hHh]; nlinarith
      have hstrict : 48 * (H * (K + 1) + K - 3) < 31 * (H * (2 * K)) := by
        rw [hKk, hHh]
        have hexact :
            31 * ((h + 6) * (2 * (k + 5))) =
            48 * ((h + 6) * (k + 5 + 1) + (k + 5) - 3) +
              (36 + 22 * h + 36 * k + 14 * h * k) := by
          have hsub : (h + 6) * (k + 5 + 1) + (k + 5) - 3 =
              (h + 6) * (k + 6) + k + 2 := by
            rw [show k + 5 + 1 = k + 6 by omega]
            omega
          rw [hsub]; ring
        omega
      have hmul : 48 * C_tot < 31 * (H * (2 * K)) :=
        (Nat.mul_le_mul_left 48 hfull).trans_lt hstrict
      exact ⟨hmul.le, fun heq => by omega⟩

end FullRankOptimality

#print axioms four_noncollinear_meeting_excess_le
#print axioms four_noncollinear_cubics_le_twelve
#print axioms four_noncollinear_septics_le_28
#print axioms label_core_conservation
#print axioms discrete_johnson_hull
#print axioms continuous_johnson_hull
#print axioms p2_head_count_barriers
#print axioms p1_quarter_five_plus_barrier
#print axioms p2_eighth_collinear_barrier
#print axioms full_rank_planar_core_cap
#print axioms second_prime_half_full_rank_optimal

end ArkLib.ProximityGap.Frontier.PlanarSharpnessAndBarriers
