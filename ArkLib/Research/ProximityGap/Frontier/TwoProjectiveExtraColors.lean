/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoProjectiveExtraWitness

/-! # Four disjoint split fibers supply the two extra projective witnesses -/
noncomputable section
open Finset Polynomial Code _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.TwoProjectiveExtraColors

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I] [Field F] [Fintype F] [DecidableEq F]

/-- Coincidence pattern of the zero polynomial, the second head and the two
outside polynomials on the four root fibers, the common locator, and the remaining sites. -/
def pattern : Fin 8 → Fin 4 → Fin 4 :=
  ![![0, 0, 2, 3], ![0, 1, 0, 0], ![0, 1, 1, 3], ![0, 1, 2, 1], ![0, 0, 0, 0],
    ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]

/-- Each of the four split fibers has D sites. R is the shared locator size. -/
def weight (D R P T : ℕ) : Fin 8 → ℕ := ![D, D, D, D, R, P + D, P, T]

private def owners (j : Fin 2) : Fin 8 → Fin 4 := ![0, 0, 1, 1, 0, 0, 1, if j = 0 then 2 else 3]
private def head (j : Fin 2) : Fin 4 := ![0, 1] j
private def extra (j : Fin 2) : Fin 4 := ![2, 3] j
private def cores : Fin 2 → Finset (Fin 8) := ![{0, 1, 4, 5}, {0, 2, 3, 4, 6}]
private def supports : Fin 2 → Finset (Fin 8) := ![{1, 2, 4, 7}, {1, 3, 4, 7}]

/-- Two full secants and both row directions give a sharp simultaneous count for
the eight-class construction, with a single received pair. -/
theorem mass (dom : I ↪ F) (k D R P T : ℕ) (δ : ℝ≥0) (f : Fin 4 → F[X]) (col : I → Fin 8)
    (deg : ∀ j, (f j).natDegree + 1 < k)
    (eq : ∀ j l i, (f j).eval (dom i) = (f l).eval (dom i) ↔ pattern (col i) j = pattern (col i) l)
    (count : ∀ j, (univ.filter (fun i => col i = j)).card = weight D R P T j)
    (hd : 0 < D) (rank : k ≤ R + 3 * D + P) (hc : k ≤ T)
    (big : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((R + 3 * D + P + 1 : ℕ) : ℝ≥0))
    (height : (1 - δ) * (Fintype.card I : ℝ≥0) ≤ ((R + 2 * D + T : ℕ) : ℝ≥0))
    (hq : (2 * (Fintype.card I - (R + 3 * D + P)) + 1).choose 2 < Fintype.card F)
    (room : 2 * (Fintype.card I - (R + 3 * D + P)) + 1 < Fintype.card F) :
    ((2 * (Fintype.card I - (R + 3 * D + P)) + 2 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤
      epsMCA (F := F) (ReedSolomon.code dom k : Set (I → F)) δ := by
  classical
  let sel (J : Finset (Fin 8)) := univ.filter fun i => col i ∈ J
  let val (j : Fin 4) (i : I) := (f j).eval (dom i)
  let row (j : Fin 2) (i : I) := val (owners j (col i)) i
  have card (J : Finset (Fin 8)) : (sel J).card = ∑ j ∈ J, weight D R P T j := by
    rw [← sum_card_fiberwise_eq_card_filter univ J col]
    exact sum_congr rfl fun j _ => count j
  have nr (j : Fin 2) : (sel (cores j)).card = R + 3 * D + P := by
    rw [card]; fin_cases j <;> simp [cores, weight] <;> omega
  have ns (j : Fin 2) : (sel (supports j)).card = R + 2 * D + T := by
    rw [card]; fin_cases j <;> simp [supports, weight] <;> omega
  have exists_fiber (j : Fin 8) (h : 0 < weight D R P T j) : ∃ i, col i = j := by
    obtain ⟨i, hi⟩ := card_pos.mp ((count j).symm ▸ h)
    exact ⟨i, (mem_filter.mp hi).2⟩
  let a : TwoProjectiveExtraWitness.Arrangement dom k δ := {
    head := fun j => f (head j)
    extra := fun j => f (extra j)
    row := row
    core := fun j => sel (cores j)
    support := fun j => sel (supports j)
    common := sel {7}
    degree := fun j => deg _
    extra_degree := fun j => deg _
    rank := fun j => (nr j).symm ▸ rank
    size := fun j => (nr j).symm ▸ big
    core_agrees := by
      intro j i
      change val _ i = val _ i ↔ _
      rw [show ∀ a b, val a i = val b i ↔ _ from fun a b => eq a b i]
      simp only [sel, mem_filter, mem_univ, true_and]
      exact (by decide : ∀ j c, pattern c (head j) = pattern c (owners 0 c) ↔ c ∈ cores j) j _
    common_rows := by
      intro j i hi
      apply (eq _ _ i).mpr
      exact (by decide : ∀ j c, c ∈ cores j → pattern c (owners 1 c) = pattern c (owners 0 c))
        j _ (mem_filter.mp hi).2
    fresh := by
      intro j i hi e
      have h := (eq _ _ i).mp e
      apply hi
      exact mem_filter.mpr ⟨mem_univ _, (by decide : ∀ j c,
        pattern c (owners 1 c) = pattern c (head j) → c ∈ cores j) j _ h⟩
    slopes := by
      intro i h₀ h₁
      have c : col i = 7 := (by decide : ∀ c, c ∉ cores 0 → c ∉ cores 1 → c = 7) _
        (fun h => h₀ (mem_filter.mpr ⟨mem_univ _, h⟩)) (fun h => h₁ (mem_filter.mpr ⟨mem_univ _, h⟩))
      have ne (j l : Fin 4) (h : j ≠ l) : val j i ≠ val l i := fun e => h (by
        have t := (eq j l i).mp e
        rw [c] at t
        exact (by decide : ∀ j l, pattern 7 j = pattern 7 l → j = l) j l t)
      change (val (owners 1 (col i)) i - val (head 0) i) / _ ≠ _
      simp only [row, c]
      change (val 3 i - val 0 i) / (val 2 i - val 0 i) ≠ (val 3 i - val 1 i) / (val 2 i - val 1 i)
      intro h
      have hx := (div_eq_div_iff (sub_ne_zero.mpr (ne 2 0 (by decide)))
        (sub_ne_zero.mpr (ne 2 1 (by decide)))).mp h
      have bad : (val 0 i - val 1 i) * (val 2 i - val 3 i) = 0 := by linear_combination -hx
      exact (mul_ne_zero (sub_ne_zero.mpr (ne 0 1 (by decide))) (sub_ne_zero.mpr (ne 2 3 (by decide)))) bad
    common_rank := by simpa [card, weight] using hc
    common_in := by
      intro j i hi
      exact mem_filter.mpr ⟨mem_univ _, (by decide : ∀ j c, c ∈ ({7} : Finset (Fin 8)) →
        c ∈ supports j) j _ (mem_filter.mp hi).2⟩
    extra_agrees := by
      intro j i hi
      apply (eq _ _ i).mpr
      exact (by decide : ∀ j c, c ∈ supports j → pattern c (extra j) = pattern c (owners j c))
        j _ (mem_filter.mp hi).2
    support_size := fun j => (ns j).symm ▸ height
    first_mismatch := by
      obtain ⟨i, hi⟩ := exists_fiber 2 hd
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, hi ▸ by decide⟩, ?_, ?_⟩
      · exact fun h => (by decide : (2 : Fin 8) ∉ cores 0) (hi ▸ (mem_filter.mp h).2)
      · intro e
        have a := (eq _ _ i).mp e
        rw [hi] at a
        exact (by decide : pattern 2 (extra 1) ≠ pattern 2 (owners 1 2)) a
    second_mismatch := by
      obtain ⟨i, hi⟩ := exists_fiber 3 hd
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, hi ▸ by decide⟩, fun e => ?_⟩
      have a := (eq _ _ i).mp e
      rw [hi] at a
      exact (by decide : pattern 3 (extra 0) ≠ pattern 3 (owners 0 3)) a }
  have cnt : 2 * (Fintype.card I - (R + 3 * D + P)) = ∑ j, (a.core j)ᶜ.card := by
    change _ = ∑ j, (sel (cores j))ᶜ.card
    simp [card_compl, nr, two_mul]
  obtain ⟨u, G, hcard, good⟩ := TwoProjectiveExtraWitness.witnesses a _ cnt hq room
  rw [← hcard]
  exact MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set _ δ u G good

#print axioms mass
end ArkLib.ProximityGap.Frontier.TwoProjectiveExtraColors
