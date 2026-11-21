/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.AffineListIncidences

/-! # One agreement anchor reduces a quadratic list to an affine incidence configuration -/
noncomputable section
open Finset Code Polynomial
namespace ProximityGap.QuadraticListIncidences
open AffineListIncidences

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

omit [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I] in
/-- A list of quadratics through a prescribed center value becomes a list of affine
polynomials after subtracting that value and dividing by the linear factor. -/
private theorem line_at (dom : I ↪ F) (w : I → F) (hw : w ∈ ReedSolomon.code dom 3) (a : I) :
    ∃ l : F × F, ∀ i, w i = w a + (dom i - dom a) * (l.1 * dom i + l.2) := by
  obtain ⟨p, hd, eval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hw
  have eval2 (i : I) : w i = p.coeff 0 + p.coeff 1 * dom i + p.coeff 2 * (dom i) ^ 2 := by
    rw [← eval]
    nth_rw 1 [p.as_sum_range_C_mul_X_pow' hd]
    simp [sum_range_succ]
  refine ⟨(p.coeff 2, p.coeff 1 + p.coeff 2 * dom a), fun i => ?_⟩
  rw [eval2, eval2]
  ring

/-- The interpolation cost need only hold for the affine list shortened at one
well-populated site. All finite interleaving widths obey the resulting budget. -/
theorem list_bound (dom : I ↪ F) (n t B l : ℕ) (hn : Fintype.card I = n)
    (ht : t ≤ n) (hl : 0 < l) (havg : n * (l - 1) < (B + 1) * t)
    (hfield : (B + 1).choose 2 ≤ Nat.card F)
    (estimate : ∀ P L : Finset (F × F), P.card = n - 1 → L.card = l →
      incidences P L < l * (t - 1)) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ B := by
  classical
  apply InterleavedListProjection.interleaved_le_of_scalar_le _ _ _ hfield
  apply Lambda_le_of_forall_finset_card_le
  intro y T hall
  by_contra! hto
  obtain ⟨S, sub, hs⟩ := exists_subset_card_eq (show B + 1 ≤ T.card by omega)
  let hit (w : I → F) := univ.filter (fun i => y i = w i)
  have large (w : I → F) (hw : w ∈ S) : t ≤ (hit w).card := by
    have close := (mem_closeCodewordsRel_iff.mp (hall w (sub hw))).2
    rw [relHammingDist_coe, hn] at close
    have pos : (0 : ℝ) < n := by exact_mod_cast hn ▸ Fintype.card_pos (α := I)
    have dist : hammingDist y w ≤ n - t := by
      exact_mod_cast (div_le_div_iff_of_pos_right pos).mp close
    have both := card_filter_add_card_filter_not (s := (univ : Finset I)) (p := fun i => y i = w i)
    change (hit w).card + hammingDist y w = _ at both
    rw [card_univ, hn] at both
    omega
  let slice (i : I) := S.filter fun w => y i = w i
  obtain ⟨a, ha⟩ : ∃ a, l ≤ (slice a).card := by
    by_contra! h
    have low : S.card * t ≤ ∑ w ∈ S, (hit w).card := by
      simpa using sum_le_sum large
    have high : ∑ i : I, (slice i).card ≤ n * (l - 1) := by
      simpa [hn] using sum_le_sum (s := (univ : Finset I))
        (fun i _ => show (slice i).card ≤ l - 1 by have := h i; omega)
    have eq : ∑ w ∈ S, (hit w).card = ∑ i : I, (slice i).card := by
      simp only [hit, slice, card_eq_sum_ones, sum_filter]
      rw [sum_comm]
    rw [hs, eq] at low
    exact havg.not_ge (low.trans high)
  obtain ⟨V, vsub, vcard⟩ := exists_subset_card_eq ha
  have member (w : V) : w.val ∈ S := (mem_filter.mp (vsub w.property)).1
  have anchor (w : V) : y a = w.val a := (mem_filter.mp (vsub w.property)).2
  choose line hline using fun w : V =>
    line_at dom w.val (mem_closeCodewordsRel_iff.mp (hall w.val (sub (member w)))).1 a
  have inj : Function.Injective line := by
    intro a₁ a₂ eq
    apply Subtype.ext
    funext i
    exact (hline a₁ i).trans (by rw [← anchor, eq, anchor a₂, ← hline])
  let word (i : I) := (y i - y a) / (dom i - dom a)
  let point (i : I) := (dom i, word i)
  have pinj : Function.Injective point := fun _ _ h => dom.injective (congrArg Prod.fst h)
  let points := (univ.erase a).image point
  let lines := (univ : Finset V).image line
  have mcount : points.card = n - 1 := by
    simp [points, card_image_of_injective _ pinj, card_erase_of_mem, hn]
  have lcount : lines.card = l := by simp [lines, card_image_of_injective _ inj, vcard]
  have mass (w : V) : t - 1 ≤ (points.filter (fun p => p.2 = (line w).1 * p.1 + (line w).2)).card := by
    have mema : a ∈ hit w.val := mem_filter.mpr ⟨mem_univ _, anchor w⟩
    have le : t - 1 ≤ ((hit w.val).erase a).card := by
      rw [card_erase_of_mem mema]
      exact Nat.sub_le_sub_right (large w.val (member w)) 1
    apply le.trans
    rw [← card_image_of_injective ((hit w.val).erase a) pinj]
    apply card_le_card
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨ia, hi⟩ := mem_erase.mp hi
    refine mem_filter.mpr ⟨mem_image_of_mem _ (mem_erase.mpr ⟨ia, mem_univ _⟩), ?_⟩
    have matchi := (mem_filter.mp hi).2
    have nd : dom i - dom a ≠ 0 := sub_ne_zero.mpr (dom.injective.ne ia)
    change (y i - y a) / (dom i - dom a) = _
    rw [div_eq_iff nd, matchi, hline w i, ← anchor w]
    ring
  have lower : l * (t - 1) ≤ incidences points lines := by
    simp only [incidences, lines, sum_image inj.injOn]
    simpa [vcard] using sum_le_sum (s := (univ : Finset V)) (fun w _ => mass w)
  exact (estimate points lines mcount lcount).not_ge lower

/-- With a budget of eight times the domain length only 44,429 agreements are required. -/
theorem eight_lengths (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (8589934593 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 71085)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      ((1073697395 : ℝ) / 1073741824) ≤ (8589934592 : ℕ) :=
  list_bound dom 1073741824 44429 8589934592 355433 hn (by decide) (by decide) (by decide) hfield
    (fun P L m s => by
      have h := graph P L
      rw [m, s] at h
      exact h.trans_lt (by decide)) width

/-- With a budget of 64 times the domain length only 26,412 agreements are required. -/
theorem sixty_four_lengths (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (68719476737 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 120739)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      ((1073715412 : ℝ) / 1073741824) ≤ (68719476736 : ℕ) :=
  list_bound dom 1073741824 26412 68719476736 1690369 hn (by decide) (by decide) (by decide) hfield
    (fun P L m s => by
      have h := graph P L
      rw [m, s] at h
      exact h.trans_lt (by decide)) width

#print axioms eight_lengths
#print axioms sixty_four_lengths
end ProximityGap.QuadraticListIncidences
