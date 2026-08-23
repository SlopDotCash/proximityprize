/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloor

/-!
# The universal cyclic floor at `r = 3` (#444, #389)

The all-`r` swap floor gives the hypothesis-free permutation contribution
`E_r(G) ≥ 2|G|^r - |G|^(r-1)`.  At the first genuinely higher rung `r = 3`, the cyclic subgroup
of the coordinate-permutation group gives a larger closed form:

> **`rEnergy_three_ge_cyclic_floor`.** `3|G|^3 - 2|G| ≤ rEnergy G 3`.

For each triple `v`, the three cyclic rotations have the same coordinate sum.  They are three
distinct witnesses unless `v` is constant, and a single witness when `v` is constant.  Therefore the
per-triple contribution is at least `3` off the constant diagonal and at least `1` on it, giving
`3|G|^3 - 2·#{constant triples} = 3|G|^3 - 2|G|`.

This is still purely char-free/permutation-symmetry bookkeeping.  It does **not** give an upper
bound, a char-`p` transfer, or a CORE closure.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def rot1 (v : Fin 3 → F) : Fin 3 → F :=
  fun i => if i = 0 then v 1 else if i = 1 then v 2 else v 0

private def rot2 (v : Fin 3 → F) : Fin 3 → F :=
  fun i => if i = 0 then v 2 else if i = 1 then v 0 else v 1

private theorem sum_rot1 (v : Fin 3 → F) :
    ∑ i, rot1 v i = ∑ i, v i := by
  simp [rot1, Fin.sum_univ_succ]
  abel

private theorem sum_rot2 (v : Fin 3 → F) :
    ∑ i, rot2 v i = ∑ i, v i := by
  simp [rot2, Fin.sum_univ_succ]
  abel

private theorem rot1_mem {G : Finset F} {v : Fin 3 → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 3 => G)) :
    rot1 v ∈ Fintype.piFinset (fun _ : Fin 3 => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i
  unfold rot1
  by_cases h0 : i = 0
  · simp [h0, hv]
  · by_cases h1 : i = 1
    · simp [h0, h1, hv]
    · simp [h0, h1, hv]

private theorem rot2_mem {G : Finset F} {v : Fin 3 → F}
    (hv : v ∈ Fintype.piFinset (fun _ : Fin 3 => G)) :
    rot2 v ∈ Fintype.piFinset (fun _ : Fin 3 => G) := by
  rw [Fintype.mem_piFinset] at hv ⊢
  intro i
  unfold rot2
  by_cases h0 : i = 0
  · simp [h0, hv]
  · by_cases h1 : i = 1
    · simp [h0, h1, hv]
    · simp [h0, h1, hv]

private theorem constant_of_rot1_eq {v : Fin 3 → F} (h : rot1 v = v) :
    v 0 = v 1 ∧ v 1 = v 2 := by
  constructor
  · have h0 := congrFun h (0 : Fin 3)
    simpa [rot1] using h0.symm
  · have h1 := congrFun h (1 : Fin 3)
    simpa [rot1] using h1.symm

private theorem constant_of_rot2_eq {v : Fin 3 → F} (h : rot2 v = v) :
    v 0 = v 1 ∧ v 1 = v 2 := by
  constructor
  · have h1 := congrFun h (1 : Fin 3)
    simpa [rot2] using h1
  · have h2 := congrFun h (2 : Fin 3)
    simpa [rot2] using h2

private theorem constant_of_rot1_eq_rot2 {v : Fin 3 → F} (h : rot1 v = rot2 v) :
    v 0 = v 1 ∧ v 1 = v 2 := by
  constructor
  · have h2 := congrFun h (2 : Fin 3)
    simpa [rot1, rot2] using h2
  · have h0 := congrFun h (0 : Fin 3)
    simpa [rot1, rot2] using h0

private theorem constantTriples_count (G : Finset F) :
    ((Fintype.piFinset (fun _ : Fin 3 => G)).filter
        (fun v => v 0 = v 1 ∧ v 1 = v 2)).card = G.card := by
  classical
  refine Finset.card_nbij'
      (fun v => v 0)
      (fun a => fun _ : Fin 3 => a)
      ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    exact hv.1 0
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · intro i
      exact ha
    · simp
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hv
    funext i
    fin_cases i
    · simp
    · exact hv.2.1
    · exact hv.2.1.trans hv.2.2
  · intro a ha
    simp


/-- The exact arithmetic gap between the `r = 3` cyclic floor and the `r = 3`
specialization of the all-`r` swap floor, recorded in `ℤ` to avoid truncating subtraction.
The cyclic-orbit improvement over the adjacent-swap floor is precisely `n(n-1)(n+2)`. -/
theorem cyclic_floor_three_gap_eq_int (n : ℤ) :
    (3 * n ^ 3 - 2 * n) - (2 * n ^ 3 - n ^ 2) = n * (n - 1) * (n + 2) := by
  ring

/-- At `r = 3`, the cyclic floor dominates the `r = 3` specialization of the all-`r`
swap floor.  This pins the first higher permutation rung as a genuine improvement over the
single-transposition floor, still by pure char-free bookkeeping. -/
theorem swap_floor_le_cyclic_floor_three (n : ℕ) :
    2 * n ^ 3 - n ^ 2 ≤ 3 * n ^ 3 - 2 * n := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  ring_nf
  omega

/-- For every nontrivial support size `n ≥ 2`, the `r = 3` cyclic floor is **strictly** above
the all-`r` swap-floor specialization.  The exact positive gap is `n(n-1)(n+2)`. -/
theorem swap_floor_lt_cyclic_floor_three_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    2 * n ^ 3 - n ^ 2 < 3 * n ^ 3 - 2 * n := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  ring_nf
  omega

/-- The exact arithmetic gap between the `r = 3` cyclic floor and the diagonal floor `n^3`,
recorded in `ℤ` to avoid truncating subtraction.  The extra cyclic-orbit supply beyond the
universal diagonal contribution is `2n(n-1)(n+1)`. -/
theorem cyclic_floor_three_diagonal_gap_eq_int (n : ℤ) :
    (3 * n ^ 3 - 2 * n) - n ^ 3 = 2 * n * (n - 1) * (n + 1) := by
  ring

/-- At `r = 3`, the cyclic floor also dominates the universal diagonal floor `n^3`. -/
theorem diagonal_floor_le_cyclic_floor_three (n : ℕ) :
    n ^ 3 ≤ 3 * n ^ 3 - 2 * n := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  ring_nf
  omega

/-- For every nontrivial support size `n ≥ 2`, the `r = 3` cyclic floor is **strictly** above
the diagonal floor.  The exact positive gap is `2n(n-1)(n+1)`. -/
theorem diagonal_floor_lt_cyclic_floor_three_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    n ^ 3 < 3 * n ^ 3 - 2 * n := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · omega
  ring_nf
  omega

/-- **The universal cyclic floor at the first higher rung.**  For every finite `G`,
`3|G|^3 - 2|G| ≤ rEnergy G 3`, by counting the three cyclic rotations of each triple, with the
only collision being the constant triples. -/
theorem rEnergy_three_ge_cyclic_floor (G : Finset F) :
    3 * G.card ^ 3 - 2 * G.card ≤ rEnergy G 3 := by
  classical
  unfold rEnergy
  have hinner : ∀ v ∈ Fintype.piFinset (fun _ : Fin 3 => G),
      (if v 0 = v 1 ∧ v 1 = v 2 then (1 : ℕ) else 3) ≤
        ∑ w ∈ Fintype.piFinset (fun _ : Fin 3 => G),
          (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
    intro v hv
    by_cases hc : v 0 = v 1 ∧ v 1 = v 2
    · simp only [hc, if_true]
      calc (1 : ℕ)
          = (if ∑ i, v i = ∑ i, v i then 1 else 0) := by simp
        _ ≤ _ := Finset.single_le_sum
              (f := fun w => if ∑ i, v i = ∑ i, w i then (1 : ℕ) else 0)
              (fun w _ => by positivity) hv
    · simp only [hc, if_false]
      have h1mem : rot1 v ∈ Fintype.piFinset (fun _ : Fin 3 => G) := rot1_mem hv
      have h2mem : rot2 v ∈ Fintype.piFinset (fun _ : Fin 3 => G) := rot2_mem hv
      have hv_ne_h1 : v ≠ rot1 v := by
        intro h; exact hc (constant_of_rot1_eq h.symm)
      have hv_ne_h2 : v ≠ rot2 v := by
        intro h; exact hc (constant_of_rot2_eq h.symm)
      have h1_ne_h2 : rot1 v ≠ rot2 v := by
        intro h; exact hc (constant_of_rot1_eq_rot2 h)
      have hsum1 : ∑ i, v i = ∑ i, rot1 v i := (sum_rot1 v).symm
      have hsum2 : ∑ i, v i = ∑ i, rot2 v i := (sum_rot2 v).symm
      have hsum12 : ∑ i, rot1 v i = ∑ i, rot2 v i := by rw [sum_rot1, sum_rot2]
      have hset : ({v, rot1 v, rot2 v} : Finset (Fin 3 → F)) ⊆
          Fintype.piFinset (fun _ : Fin 3 => G) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hv
        · exact h1mem
        · exact h2mem
      calc (3 : ℕ)
          = ∑ w ∈ ({v, rot1 v, rot2 v} : Finset (Fin 3 → F)),
              (if ∑ i, v i = ∑ i, w i then 1 else 0) := by
            rw [Finset.sum_insert]
            · rw [Finset.sum_insert]
              · rw [Finset.sum_singleton]
                simp [hsum1, hsum2, hsum12]
              · simp [h1_ne_h2]
            · simp [hv_ne_h1, hv_ne_h2]
        _ ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin 3 => G),
              (if ∑ i, v i = ∑ i, w i then 1 else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg hset (fun w _ _ => by positivity)
  have hsum_lhs : ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => G),
      (if v 0 = v 1 ∧ v 1 = v 2 then (1 : ℕ) else 3)
      = 3 * G.card ^ 3 - 2 * G.card := by
    have hcard_pi : (Fintype.piFinset (fun _ : Fin 3 => G)).card = G.card ^ 3 := by
      rw [Fintype.card_piFinset_const]
    have hpoint : ∀ v : Fin 3 → F,
        (if v 0 = v 1 ∧ v 1 = v 2 then (1 : ℕ) else 3)
        = 3 - 2 * (if v 0 = v 1 ∧ v 1 = v 2 then 1 else 0) := by
      intro v; by_cases h : v 0 = v 1 ∧ v 1 = v 2 <;> simp [h]
    simp_rw [hpoint]
    rw [Finset.sum_tsub_distrib _ (fun v _ => by
          by_cases h : v 0 = v 1 ∧ v 1 = v 2 <;> simp [h])]
    rw [Finset.sum_const, hcard_pi, smul_eq_mul]
    have hcount : ∑ v ∈ Fintype.piFinset (fun _ : Fin 3 => G),
        (if v 0 = v 1 ∧ v 1 = v 2 then (1 : ℕ) else 0) = G.card := by
      rw [Finset.sum_boole]
      simp only [Nat.cast_id]
      exact constantTriples_count G
    have hcount2 : ∑ x ∈ Fintype.piFinset (fun _ : Fin 3 => G),
        2 * (if x 0 = x 1 ∧ x 1 = x 2 then (1 : ℕ) else 0) = 2 * G.card := by
      rw [← Finset.mul_sum, hcount]
    rw [hcount2, Nat.mul_comm (G.card ^ 3) 3]
  rw [← hsum_lhs]
  exact Finset.sum_le_sum hinner

end ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

#print axioms rEnergy_three_ge_cyclic_floor

#print axioms cyclic_floor_three_gap_eq_int
#print axioms swap_floor_le_cyclic_floor_three
#print axioms swap_floor_lt_cyclic_floor_three_of_two_le
#print axioms cyclic_floor_three_diagonal_gap_eq_int
#print axioms diagonal_floor_le_cyclic_floor_three
#print axioms diagonal_floor_lt_cyclic_floor_three_of_two_le

end ArkLib.ProximityGap.SubgroupGaussSumMoment
