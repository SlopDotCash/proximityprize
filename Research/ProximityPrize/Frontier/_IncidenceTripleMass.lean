/-
Copyright (c) 2026 Mikhail Izhutkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mikhail Izhutkin (mashingaan, @mashingaan)
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.CoveragePigeonhole

set_option autoImplicit false
namespace ProximityGap.IncidenceTripleMass

/-- The integer-degree triple incidence mass uses this division-free cube bound. -/
theorem cube_sum_le_card_sq_mul_sum_cube
    {I : Type} [Fintype I] [Nonempty I]
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∑ i, d i) ^ 3 ≤ (Fintype.card I : ℝ) ^ 2 * ∑ i, (d i) ^ 3 := by
  classical
  let N : ℝ := Fintype.card I
  let S : ℝ := ∑ i, d i
  let mean : ℝ := S / N
  have hN : 0 < N := by
    change 0 < (Fintype.card I : ℝ)
    exact_mod_cast (show 0 < Fintype.card I from Fintype.card_pos)
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hd i)
  have hm : 0 ≤ mean := div_nonneg hS0 hN.le
  have hS : S = mean * N := by
    dsimp [mean]
    rw [div_mul_cancel₀ _ (ne_of_gt hN)]
  have hterm : ∀ i, 3 * mean ^ 2 * d i - 2 * mean ^ 3 ≤ (d i) ^ 3 := by
    intro i
    have hpos : 0 ≤ d i + 2 * mean :=
      add_nonneg (hd i) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm)
    have hp := mul_nonneg (sq_nonneg (d i - mean)) hpos
    nlinarith
  have hmean : N * mean ^ 3 ≤ ∑ i, (d i) ^ 3 := by
    calc
      N * mean ^ 3 = ∑ i, (3 * mean ^ 2 * d i - 2 * mean ^ 3) := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change N * mean ^ 3 = 3 * mean ^ 2 * S - 2 * (N * mean ^ 3)
        rw [hS]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hterm i)
  have hmul := mul_le_mul_of_nonneg_left hmean (sq_nonneg N)
  change S ^ 3 ≤ N ^ 2 * ∑ i, (d i) ^ 3
  calc
    S ^ 3 = N ^ 2 * (N * mean ^ 3) := by
      rw [hS]
      ring
    _ ≤ _ := hmul

theorem nat_cube_sum_le_card_sq_mul_sum_cube
    {I : Type} [Fintype I] [Nonempty I] (d : I → ℕ) :
    (∑ i, d i) ^ 3 ≤ (Fintype.card I) ^ 2 * ∑ i, (d i) ^ 3 := by
  have h := cube_sum_le_card_sq_mul_sum_cube
    (fun i => (d i : ℝ)) (fun i => Nat.cast_nonneg (d i))
  dsimp only at h
  exact_mod_cast h

theorem sum_card_triple_inter_eq_sum_degree_cube
    {I X : Type} [Fintype I] [Fintype X] [DecidableEq X]
    (S : I → Finset X) :
    (∑ i, ∑ j, ∑ k, (S i ∩ S j ∩ S k).card) =
      ∑ x : X, (Finset.univ.filter (fun i => x ∈ S i)).card ^ 3 := by
  classical
  let v : I → X → ℕ := fun i x => if x ∈ S i then 1 else 0
  let f : I → I → I → X → ℕ := fun i j k x => v i x * v j x * v k x
  have hcard : ∀ i j k, (S i ∩ S j ∩ S k).card = ∑ x, f i j k x := by
    intro i j k
    calc
      (S i ∩ S j ∩ S k).card =
          (Finset.univ.filter (fun x => x ∈ S i ∩ S j ∩ S k)).card := by
        congr 1
        ext x
        simp
      _ = ∑ x, (if x ∈ S i ∩ S j ∩ S k then 1 else 0) := by
        rw [Finset.card_filter]
      _ = ∑ x, f i j k x := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [f, v]
        by_cases hi : x ∈ S i
        · by_cases hj : x ∈ S j
          · simp [hi, hj]
          · simp [hi, hj]
        · simp [hi]
  have hdeg : ∀ x : X, (Finset.univ.filter (fun i => x ∈ S i)).card =
      ∑ i, v i x := by
    intro x
    rw [Finset.card_filter]
  have hswap : (∑ i, ∑ j, ∑ k, ∑ x, f i j k x) =
      ∑ x, ∑ i, ∑ j, ∑ k, f i j k x := by
    calc
      _ = ∑ i, ∑ j, ∑ x, ∑ k, f i j k x := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ j, ∑ k, f i j k x := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp_rw [hcard]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro x hx
  rw [hdeg]
  dsimp [f]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem triple_union_mass_bound
    {I X : Type} [Fintype I] [Fintype X] [Nonempty X] [DecidableEq X]
    (E : I → Finset X) (t : ℕ) (hE : ∀ i, (E i).card = t) :
    (Fintype.card X) ^ 2 * (∑ i, ∑ j, ∑ k, (E i ∪ E j ∪ E k).card) +
      (Fintype.card I * (Fintype.card X - t)) ^ 3 ≤
        (Fintype.card X) ^ 3 * (Fintype.card I) ^ 3 := by
  classical
  let T : I → Finset X := fun i => (E i)ᶜ
  have hT : ∀ i, (T i).card = Fintype.card X - t := by
    intro i
    simp only [T, Finset.card_compl, hE i]
  have hsum : (∑ x : X, (Finset.univ.filter (fun i => x ∈ T i)).card) =
      Fintype.card I * (Fintype.card X - t) := by
    rw [← ArkLib.Coverage.sum_card_eq_sum_degree T]
    simp only [hT, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hc := nat_cube_sum_le_card_sq_mul_sum_cube
    (fun x : X => (Finset.univ.filter (fun i => x ∈ T i)).card)
  rw [hsum, ← sum_card_triple_inter_eq_sum_degree_cube T] at hc
  have hpoint : ∀ i j k, (T i ∩ T j ∩ T k).card +
      (E i ∪ E j ∪ E k).card = Fintype.card X := by
    intro i j k
    have hcomp : (E i ∪ E j ∪ E k)ᶜ = T i ∩ T j ∩ T k := by
      ext x
      simp [T, not_or]
    have hh := Finset.card_compl_add_card (E i ∪ E j ∪ E k)
    rw [hcomp] at hh
    exact hh
  have hmass : (∑ i, ∑ j, ∑ k, (T i ∩ T j ∩ T k).card) +
      (∑ i, ∑ j, ∑ k, (E i ∪ E j ∪ E k).card) =
      Fintype.card X * (Fintype.card I) ^ 3 := by
    calc
      _ = ∑ i : I, ∑ j : I, ∑ k : I, Fintype.card X := by
        simp_rw [← Finset.sum_add_distrib, hpoint]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring
  calc
    _ ≤ (Fintype.card X) ^ 2 *
        (∑ i, ∑ j, ∑ k, (E i ∪ E j ∪ E k).card) +
      (Fintype.card X) ^ 2 *
        (∑ i, ∑ j, ∑ k, (T i ∩ T j ∩ T k).card) :=
      Nat.add_le_add_left hc _
    _ = _ := by
      rw [← Nat.mul_add, Nat.add_comm
        (∑ i, ∑ j, ∑ k, (E i ∪ E j ∪ E k).card)
        (∑ i, ∑ j, ∑ k, (T i ∩ T j ∩ T k).card), hmass]
      ring

end ProximityGap.IncidenceTripleMass
#print axioms ProximityGap.IncidenceTripleMass.cube_sum_le_card_sq_mul_sum_cube

#print axioms ProximityGap.IncidenceTripleMass.nat_cube_sum_le_card_sq_mul_sum_cube
#print axioms ProximityGap.IncidenceTripleMass.sum_card_triple_inter_eq_sum_degree_cube

#print axioms ProximityGap.IncidenceTripleMass.triple_union_mass_bound
