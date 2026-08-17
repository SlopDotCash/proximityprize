/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergyCyclicFloorAllDepth

/-!
# The universal cyclic floor at depth four

At depth four, the full cyclic group distinguishes a new intermediate orbit type.  A quadruple has
cyclic orbit size one when it is constant, size two when it is nonconstant and two-periodic, and
size four otherwise.  Counting those rotations gives

> **`rEnergy_four_ge_cyclic_floor`.**
> `4 * |G| ^ 4 - 2 * |G| ^ 2 - |G| <= rEnergy G 4`.

There are exactly `|G|` constant quadruples and `|G| ^ 2` two-periodic quadruples.  The resulting
floor lifts through arbitrary common tails, giving a stronger all-depth cyclic floor from depth
four onward.  For `|G| >= 2`, it strictly improves the depth-three cyclic floor lifted to the same
depth.

This is pure finite permutation bookkeeping over an arbitrary finite field.  It does **not** give
an upper energy bound, a characteristic transfer, or a CORE closure.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def rot1 (v : Fin 4 -> F) : Fin 4 -> F :=
  fun i => if i = 0 then v 1 else if i = 1 then v 2 else if i = 2 then v 3 else v 0

private def rot2 (v : Fin 4 -> F) : Fin 4 -> F :=
  fun i => if i = 0 then v 2 else if i = 1 then v 3 else if i = 2 then v 0 else v 1

private def rot3 (v : Fin 4 -> F) : Fin 4 -> F :=
  fun i => if i = 0 then v 3 else if i = 1 then v 0 else if i = 2 then v 1 else v 2

private theorem sum_rot1 (v : Fin 4 -> F) :
    ∑ i, rot1 v i = ∑ i, v i := by
  simp [rot1, Fin.sum_univ_succ]
  abel

private theorem sum_rot2 (v : Fin 4 -> F) :
    ∑ i, rot2 v i = ∑ i, v i := by
  simp [rot2, Fin.sum_univ_succ]
  abel

private theorem sum_rot3 (v : Fin 4 -> F) :
    ∑ i, rot3 v i = ∑ i, v i := by
  simp [rot3, Fin.sum_univ_succ]
  abel

private theorem rot1_mem {G : Finset F} {v : Fin 4 -> F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 4 => G)) :
    rot1 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i
  fin_cases i <;> simp [rot1, hv]

private theorem rot2_mem {G : Finset F} {v : Fin 4 -> F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 4 => G)) :
    rot2 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i
  fin_cases i <;> simp [rot2, hv]

private theorem rot3_mem {G : Finset F} {v : Fin 4 -> F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 4 => G)) :
    rot3 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i
  fin_cases i <;> simp [rot3, hv]

private theorem constant_of_rot1_eq {v : Fin 4 -> F} (h : rot1 v = v) :
    v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  constructor
  · simpa [rot1] using h0.symm
  constructor
  · simpa [rot1] using h1.symm
  · simpa [rot1] using h2.symm

private theorem constant_of_rot3_eq {v : Fin 4 -> F} (h : rot3 v = v) :
    v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 := by
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  constructor
  · simpa [rot3] using h1
  constructor
  · simpa [rot3] using h2
  · simpa [rot3] using h3

private theorem constant_of_rot1_eq_rot2 {v : Fin 4 -> F} (h : rot1 v = rot2 v) :
    v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h3 := congrFun h (3 : Fin 4)
  constructor
  · simpa [rot1, rot2] using h3
  constructor
  · simpa [rot1, rot2] using h0
  · simpa [rot1, rot2] using h1

private theorem constant_of_rot2_eq_rot3 {v : Fin 4 -> F} (h : rot2 v = rot3 v) :
    v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 := by
  have h0 := congrFun h (0 : Fin 4)
  have h1 := congrFun h (1 : Fin 4)
  have h2 := congrFun h (2 : Fin 4)
  constructor
  · simpa [rot2, rot3] using h2
  constructor
  · calc
      v 1 = v 0 := by simpa [rot2, rot3] using h2.symm
      _ = v 3 := by simpa [rot2, rot3] using h1.symm
      _ = v 2 := by simpa [rot2, rot3] using h0.symm
  · simpa [rot2, rot3] using h0

private theorem periodTwo_of_rot2_eq {v : Fin 4 -> F} (h : rot2 v = v) :
    v 0 = v 2 ∧ v 1 = v 3 := by
  constructor
  · have h0 := congrFun h (0 : Fin 4)
    simpa [rot2] using h0.symm
  · have h1 := congrFun h (1 : Fin 4)
    simpa [rot2] using h1.symm

private theorem periodTwo_of_rot1_eq_rot3 {v : Fin 4 -> F} (h : rot1 v = rot3 v) :
    v 0 = v 2 ∧ v 1 = v 3 := by
  constructor
  · have h1 := congrFun h (1 : Fin 4)
    simpa [rot1, rot3] using h1.symm
  · have h0 := congrFun h (0 : Fin 4)
    simpa [rot1, rot3] using h0

private theorem constantQuadruples_count (G : Finset F) :
    ((Fintype.piFinset (fun _ : Fin 4 => G)).filter
        (fun v => v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3)).card = G.card := by
  classical
  refine Finset.card_nbij'
      (fun v => v 0)
      (fun a => fun _ : Fin 4 => a)
      ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    exact hv.1 0
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨fun _ => ha, by simp⟩
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    funext i
    fin_cases i
    · simp
    · exact hv.2.1
    · exact hv.2.1.trans hv.2.2.1
    · exact hv.2.1.trans (hv.2.2.1.trans hv.2.2.2)
  · intro a ha
    simp

private def periodTwoTuple (a : F × F) : Fin 4 -> F :=
  fun i => if i = 0 then a.1 else if i = 1 then a.2 else if i = 2 then a.1 else a.2

private theorem periodTwoQuadruples_count (G : Finset F) :
    ((Fintype.piFinset (fun _ : Fin 4 => G)).filter
        (fun v => v 0 = v 2 ∧ v 1 = v 3)).card = (G.product G).card := by
  classical
  refine Finset.card_nbij'
      (fun v => (v 0, v 1))
      periodTwoTuple
      ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    exact Finset.mem_product.mpr ⟨hv.1 0, hv.1 1⟩
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    have ha' : a.1 ∈ G ∧ a.2 ∈ G := by simpa using ha
    constructor
    · intro i
      fin_cases i <;> simp [periodTwoTuple, ha']
    · simp [periodTwoTuple]
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    funext i
    fin_cases i
    · simp [periodTwoTuple]
    · simp [periodTwoTuple]
    · simpa [periodTwoTuple] using hv.2.1
    · simpa [periodTwoTuple] using hv.2.2
  · intro a ha
    rcases a with ⟨a, b⟩
    simp [periodTwoTuple]

/-- The exact integer gap between the depth-four cyclic floor and the depth-three cyclic floor
lifted once.  The new orbit type contributes precisely `n^4 - n`. -/
theorem cyclic_floor_four_gap_eq_int (n : ℤ) :
    (4 * n ^ 4 - 2 * n ^ 2 - n) - (3 * n ^ 4 - 2 * n ^ 2) = n ^ 4 - n := by
  ring

/-- The depth-four cyclic floor dominates the depth-three cyclic floor lifted once. -/
theorem cyclic_floor_three_lift_le_cyclic_floor_four (n : ℕ) :
    3 * n ^ 4 - 2 * n ^ 2 ≤ 4 * n ^ 4 - 2 * n ^ 2 - n := by
  rcases n with _ | n
  · simp
  ring_nf
  omega

/-- For every support of size at least two, the direct depth-four cyclic floor strictly improves
the depth-three cyclic floor lifted once. -/
theorem cyclic_floor_three_lift_lt_cyclic_floor_four_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    3 * n ^ 4 - 2 * n ^ 2 < 4 * n ^ 4 - 2 * n ^ 2 - n := by
  rcases n with _ | n
  · omega
  ring_nf
  omega

/-- **The universal cyclic floor at depth four.**  The four rotations of a quadruple contribute
orbit size four, except for the `|G| ^ 2` two-periodic quadruples and the `|G|` constant ones. -/
theorem rEnergy_four_ge_cyclic_floor (G : Finset F) :
    4 * G.card ^ 4 - 2 * G.card ^ 2 - G.card ≤ rEnergy G 4 := by
  classical
  unfold rEnergy
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 4 => G),
      (if v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 then (1 : ℕ)
        else if v 0 = v 2 ∧ v 1 = v 3 then 2 else 4) ≤
        ∑ w ∈ Fintype.piFinset (fun _ : Fin 4 => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    by_cases hc : v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3
    · simp only [hc, if_true]
      calc (1 : ℕ)
          = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
        _ ≤ _ := Finset.single_le_sum
              (f := fun w => if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0)
              (fun w _ => by positivity) hv
    · simp only [hc, if_false]
      by_cases hp : v 0 = v 2 ∧ v 1 = v 3
      · simp only [hp, if_true]
        have h1mem : rot1 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := rot1_mem hv
        have hv_ne_h1 : v ≠ rot1 v := by
          intro h
          exact hc (constant_of_rot1_eq h.symm)
        have hsum1 : ∑ i, v i = ∑ i, rot1 v i := (sum_rot1 v).symm
        have hset : ({v, rot1 v} : Finset (Fin 4 -> F)) ⊆
            Fintype.piFinset (fun _ : Fin 4 => G) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hv
          · exact h1mem
        calc (2 : ℕ)
            = ∑ w ∈ ({v, rot1 v} : Finset (Fin 4 -> F)),
                (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
              rw [Finset.sum_insert]
              · rw [Finset.sum_singleton]
                simp [hsum1]
              · simpa using hv_ne_h1
          _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin 4 => G),
                (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hset (fun w _ _ => by positivity)
      · simp only [hp, if_false]
        have h1mem : rot1 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := rot1_mem hv
        have h2mem : rot2 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := rot2_mem hv
        have h3mem : rot3 v ∈ Fintype.piFinset (fun _ : Fin 4 => G) := rot3_mem hv
        have hv_ne_h1 : v ≠ rot1 v := by
          intro h
          exact hc (constant_of_rot1_eq h.symm)
        have hv_ne_h2 : v ≠ rot2 v := by
          intro h
          exact hp (periodTwo_of_rot2_eq h.symm)
        have hv_ne_h3 : v ≠ rot3 v := by
          intro h
          exact hc (constant_of_rot3_eq h.symm)
        have h1_ne_h2 : rot1 v ≠ rot2 v := by
          intro h
          exact hc (constant_of_rot1_eq_rot2 h)
        have h1_ne_h3 : rot1 v ≠ rot3 v := by
          intro h
          exact hp (periodTwo_of_rot1_eq_rot3 h)
        have h2_ne_h3 : rot2 v ≠ rot3 v := by
          intro h
          exact hc (constant_of_rot2_eq_rot3 h)
        have hsum1 : ∑ i, v i = ∑ i, rot1 v i := (sum_rot1 v).symm
        have hsum2 : ∑ i, v i = ∑ i, rot2 v i := (sum_rot2 v).symm
        have hsum3 : ∑ i, v i = ∑ i, rot3 v i := (sum_rot3 v).symm
        have hsum12 : ∑ i, rot1 v i = ∑ i, rot2 v i := by
          rw [sum_rot1, sum_rot2]
        have hsum13 : ∑ i, rot1 v i = ∑ i, rot3 v i := by
          rw [sum_rot1, sum_rot3]
        have hsum23 : ∑ i, rot2 v i = ∑ i, rot3 v i := by
          rw [sum_rot2, sum_rot3]
        have hset : ({v, rot1 v, rot2 v, rot3 v} : Finset (Fin 4 -> F)) ⊆
            Fintype.piFinset (fun _ : Fin 4 => G) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact hv
          · exact h1mem
          · exact h2mem
          · exact h3mem
        calc (4 : ℕ)
            = ∑ w ∈ ({v, rot1 v, rot2 v, rot3 v} : Finset (Fin 4 -> F)),
                (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
              rw [Finset.sum_insert]
              · rw [Finset.sum_insert]
                · rw [Finset.sum_insert]
                  · rw [Finset.sum_singleton]
                    simp [hsum1, hsum2, hsum3, hsum12, hsum13, hsum23]
                  · simpa using h2_ne_h3
                · simp [h1_ne_h2, h1_ne_h3]
              · simp [hv_ne_h1, hv_ne_h2, hv_ne_h3]
          _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin 4 => G),
                (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg hset (fun w _ _ => by positivity)
  have hsum_lhs : ∑ v ∈ Fintype.piFinset (fun _ : Fin 4 => G),
      (if v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 then (1 : ℕ)
        else if v 0 = v 2 ∧ v 1 = v 3 then 2 else 4)
      = 4 * G.card ^ 4 - 2 * G.card ^ 2 - G.card := by
    have hcard_pi : (Fintype.piFinset (fun _ : Fin 4 => G)).card = G.card ^ 4 := by
      rw [Fintype.card_piFinset_const]
    have hpoint : ∀ v : Fin 4 -> F,
        (if v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 then (1 : ℕ)
          else if v 0 = v 2 ∧ v 1 = v 3 then 2 else 4) =
        4 - 2 * (if v 0 = v 2 ∧ v 1 = v 3 then 1 else 0) -
          (if v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 then 1 else 0) := by
      intro v
      by_cases hc : v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3
      · have hp : v 0 = v 2 ∧ v 1 = v 3 :=
          ⟨hc.1.trans hc.2.1, hc.2.1.trans hc.2.2⟩
        simp only [if_pos hc, if_pos hp]
      · by_cases hp : v 0 = v 2 ∧ v 1 = v 3
        · simp only [if_neg hc, if_pos hp]
        · simp only [if_neg hc, if_neg hp]
    simp_rw [hpoint]
    rw [Finset.sum_tsub_distrib _ (fun v _ => by
          by_cases hc : v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3
          · have hp : v 0 = v 2 ∧ v 1 = v 3 :=
              ⟨hc.1.trans hc.2.1, hc.2.1.trans hc.2.2⟩
            simp only [if_pos hc, if_pos hp]
            omega
          · by_cases hp : v 0 = v 2 ∧ v 1 = v 3
            · simp only [if_neg hc, if_pos hp]
              omega
            · simp only [if_neg hc, if_neg hp]
              omega)]
    rw [Finset.sum_tsub_distrib _ (fun v _ => by
          by_cases hp : v 0 = v 2 ∧ v 1 = v 3
          · simp only [if_pos hp]
            omega
          · simp only [if_neg hp]
            omega)]
    rw [Finset.sum_const, hcard_pi, smul_eq_mul]
    have hperiod : ∑ v ∈ Fintype.piFinset (fun _ : Fin 4 => G),
        (if v 0 = v 2 ∧ v 1 = v 3 then (1 : ℕ) else 0) = G.card ^ 2 := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      simpa [Finset.card_product, pow_two] using periodTwoQuadruples_count G
    have hperiod2 : ∑ v ∈ Fintype.piFinset (fun _ : Fin 4 => G),
        2 * (if v 0 = v 2 ∧ v 1 = v 3 then (1 : ℕ) else 0) = 2 * G.card ^ 2 := by
      rw [← Finset.mul_sum, hperiod]
    have hconstant : ∑ v ∈ Fintype.piFinset (fun _ : Fin 4 => G),
        (if v 0 = v 1 ∧ v 1 = v 2 ∧ v 2 = v 3 then (1 : ℕ) else 0) = G.card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      exact constantQuadruples_count G
    rw [hperiod2, hconstant, Nat.mul_comm (G.card ^ 4) 4]
  rw [← hsum_lhs]
  exact Finset.sum_le_sum hinner

private theorem mul_four_cyclic_floor_eq (n m : ℕ) :
    n ^ m * (4 * n ^ 4 - 2 * n ^ 2 - n) =
      4 * n ^ (m + 4) - 2 * n ^ (m + 2) - n ^ (m + 1) := by
  rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
  simp only [pow_add]
  ring

private theorem mul_three_cyclic_lift_eq (n m : ℕ) :
    n ^ m * (3 * n ^ 4 - 2 * n ^ 2) =
      3 * n ^ (m + 4) - 2 * n ^ (m + 2) := by
  rw [Nat.mul_sub_left_distrib]
  simp only [pow_add]
  ring

/-- **The depth-four cyclic floor at every higher depth.**  Appending a common tail of length `m`
to both tuples lifts the direct depth-four bound without losing its orbit improvement. -/
theorem rEnergy_ge_four_cyclic_floor_all_depth (G : Finset F) (m : ℕ) :
    4 * G.card ^ (m + 4) - 2 * G.card ^ (m + 2) - G.card ^ (m + 1) ≤
      rEnergy G (m + 4) := by
  calc
    4 * G.card ^ (m + 4) - 2 * G.card ^ (m + 2) - G.card ^ (m + 1) =
        G.card ^ m * (4 * G.card ^ 4 - 2 * G.card ^ 2 - G.card) :=
      (mul_four_cyclic_floor_eq G.card m).symm
    _ ≤ G.card ^ m * rEnergy G 4 :=
      Nat.mul_le_mul_left _ (rEnergy_four_ge_cyclic_floor G)
    _ ≤ rEnergy G (4 + m) := card_pow_mul_rEnergy_le_add G 4 m
    _ = rEnergy G (m + 4) := by rw [Nat.add_comm]

/-- At every depth at least four, the direct depth-four floor dominates the depth-three cyclic
floor lifted to the same depth. -/
theorem cyclic_floor_three_lift_le_four_all_depth (n m : ℕ) :
    3 * n ^ (m + 4) - 2 * n ^ (m + 2) ≤
      4 * n ^ (m + 4) - 2 * n ^ (m + 2) - n ^ (m + 1) := by
  calc
    3 * n ^ (m + 4) - 2 * n ^ (m + 2) =
        n ^ m * (3 * n ^ 4 - 2 * n ^ 2) :=
      (mul_three_cyclic_lift_eq n m).symm
    _ ≤ n ^ m * (4 * n ^ 4 - 2 * n ^ 2 - n) :=
      Nat.mul_le_mul_left _ (cyclic_floor_three_lift_le_cyclic_floor_four n)
    _ = 4 * n ^ (m + 4) - 2 * n ^ (m + 2) - n ^ (m + 1) :=
      mul_four_cyclic_floor_eq n m

/-- For support size at least two, the depth-four floor remains strictly stronger after every
common-tail lift. -/
theorem cyclic_floor_three_lift_lt_four_all_depth_of_two_le
    {n : ℕ} (m : ℕ) (hn : 2 ≤ n) :
    3 * n ^ (m + 4) - 2 * n ^ (m + 2) <
      4 * n ^ (m + 4) - 2 * n ^ (m + 2) - n ^ (m + 1) := by
  have hpow : 0 < n ^ m := pow_pos (by omega) m
  calc
    3 * n ^ (m + 4) - 2 * n ^ (m + 2) =
        n ^ m * (3 * n ^ 4 - 2 * n ^ 2) :=
      (mul_three_cyclic_lift_eq n m).symm
    _ < n ^ m * (4 * n ^ 4 - 2 * n ^ 2 - n) :=
      Nat.mul_lt_mul_of_pos_left
        (cyclic_floor_three_lift_lt_cyclic_floor_four_of_two_le hn) hpow
    _ = 4 * n ^ (m + 4) - 2 * n ^ (m + 2) - n ^ (m + 1) :=
      mul_four_cyclic_floor_eq n m

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_four_ge_cyclic_floor
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.cyclic_floor_four_gap_eq_int
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.cyclic_floor_three_lift_le_cyclic_floor_four
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.cyclic_floor_three_lift_lt_cyclic_floor_four_of_two_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy_ge_four_cyclic_floor_all_depth
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.cyclic_floor_three_lift_le_four_all_depth
#print axioms
  ArkLib.ProximityGap.SubgroupGaussSumMoment.cyclic_floor_three_lift_lt_four_all_depth_of_two_le
