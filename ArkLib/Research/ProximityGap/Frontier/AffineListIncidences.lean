/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Dimension-two Reed–Solomon lists as point-line incidences -/
noncomputable section
open Finset Code Polynomial
namespace ProximityGap.AffineListIncidences

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- Count incidences of points with nonvertical lines given by a slope and intercept. -/
def incidences (points lines : Finset (F × F)) : ℕ :=
  ∑ l ∈ lines, (points.filter (fun p => p.2 = l.1 * p.1 + l.2)).card

/-- Integer graph bound at one interpolation degree, as in Lewko, arXiv:2609.27023v3. -/
def cost (m L d : ℕ) := m * (2 * L / (d + 2) + 1) + d * (d - 1) + L

def GraphEstimate (F : Type*) [Field F] [DecidableEq F] (d : ℕ) : Prop :=
  ∀ P L : Finset (F × F), incidences P L ≤ cost P.card L.card d

omit [Fintype F] in
/-- Slope-intercept duality exchanges the two finite sets without adding a vertical line. -/
theorem dual_bound {d : ℕ} (h : GraphEstimate F d) (points lines : Finset (F × F)) :
    incidences points lines ≤ cost lines.card points.card d := by
  classical
  let flip (p : F × F) := (p.1, -p.2)
  have inj : Function.Injective flip := by
    rintro ⟨a,b⟩ ⟨c,d⟩ e
    change (a, -b) = (c, -d) at e
    exact Prod.ext (Prod.mk.inj e).1 (neg_inj.mp (Prod.mk.inj e).2)
  have bound := h (lines.image flip) (points.image flip)
  rw [card_image_of_injective _ inj, card_image_of_injective _ inj] at bound
  apply le_trans (le_of_eq ?_) bound
  simp only [incidences, sum_image inj.injOn, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro l hl
  have eq : p.2 = l.1 * p.1 + l.2 ↔ (flip l).2 = (flip p).1 * (flip l).1 + (flip p).2 := by
    dsimp [flip]
    rw [mul_comm]; constructor <;> intro h <;> linear_combination h
  simp only [eq]

/-- If the incidence cost for one over-budget sublist is too small, the canonical
closed ball around every center meets the budget at every finite interleaving width. -/
theorem list_bound (dom : I ↪ F) (n t B : ℕ) (hn : Fintype.card I = n)
    (ht : t ≤ n) (hfield : (B + 1).choose 2 ≤ Nat.card F)
    (estimate : ∀ points lines : Finset (F × F), points.card = n → lines.card = B + 1 →
       incidences points lines < (B + 1) * t) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 2 : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ B := by
  classical
  apply InterleavedListProjection.interleaved_le_of_scalar_le _ _ _ hfield
  apply Lambda_le_of_forall_finset_card_le
  intro center T hall
  by_contra! hto
  obtain ⟨S, sub, hs⟩ := exists_subset_card_eq (show B + 1 ≤ T.card by omega)
  have rep (w : S) : ∃ l : F × F, ∀ i, w.val i = l.1 * dom i + l.2 := by
    obtain ⟨p, deg, eval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp
      (mem_closeCodewordsRel_iff.mp (hall w.val (sub w.property))).1
    refine ⟨(p.coeff 1, p.coeff 0), fun i => ?_⟩
    rw [← eval]
    nth_rw 1 [p.eq_X_add_C_of_natDegree_le_one (by omega)]
    simp
  choose coeff heval using rep
  have inj : Function.Injective coeff := by
    intro a b h
    apply Subtype.ext
    funext i
    rw [heval a i, heval b i, h]
  let points := (univ : Finset I).image (fun i => (dom i, center i))
  let lines := (univ : Finset S).image coeff
  have point_inj : Function.Injective (fun i : I => (dom i, center i)) :=
    fun _ _ h => dom.injective (congrArg Prod.fst h)
  have mcount : points.card = n := by simp [points, card_image_of_injective _ point_inj, hn]
  have lcount : lines.card = B + 1 := by simp [lines, card_image_of_injective _ inj, hs]
  have hd (w : S) : t ≤ (univ.filter (fun i => center i = w.val i)).card := by
    obtain ⟨_, close⟩ := mem_closeCodewordsRel_iff.mp (hall w.val (sub w.property))
    rw [relHammingDist_coe, hn] at close
    have pos : (0 : ℝ) < n := by exact_mod_cast hn ▸ Fintype.card_pos (α := I)
    have dist : hammingDist center w.val ≤ n - t := by
      exact_mod_cast (div_le_div_iff_of_pos_right pos).mp close
    have both := card_filter_add_card_filter_not (s := (univ : Finset I)) (p := fun i => center i = w.val i)
    change _ + hammingDist center w.val = _ at both
    rw [card_univ, hn] at both
    omega
  have mass (w : S) : t ≤ (points.filter (fun p => p.2 = (coeff w).1 * p.1 + (coeff w).2)).card := by
    apply (hd w).trans
    rw [show points.filter _ = (univ.filter (fun i => center i = w.val i)).image
        (fun i => (dom i, center i)) from ?_, card_image_of_injective _ point_inj]
    ext p
    simp only [points, mem_filter, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, rfl⟩, ha⟩
      exact ⟨i, ha.trans (heval w i).symm, rfl⟩
    · rintro ⟨i, ha, rfl⟩
      exact ⟨⟨i, rfl⟩, ha.trans (heval w i)⟩
  have low : (B + 1) * t ≤ incidences points lines := by
    simp only [incidences, lines, sum_image inj.injOn]
    simpa [hs] using sum_le_sum (s := (univ : Finset S)) (fun w _ => mass w)
  exact (estimate points lines mcount lcount).not_ge low

/-- At length 2³⁰, 3073 agreements suffice at the first named budget. -/
theorem first (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (1073741825 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 1048575)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 2 : Set (I → F)))
      ((1073738751 : ℝ) / 1073741824) ≤ (1073741824 : ℕ) :=
  list_bound dom 1073741824 3073 1073741824 hn (by decide) hfield (fun P L m l => by
    have h := graph P L
    rw [m, l] at h
    exact h.trans_lt (by decide)) width

/-- At length 2³⁰, dualizing the incidence configuration gives the second named
budget at 2439 agreements. -/
theorem second (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (2147483649 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 1320714)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 2 : Set (I → F)))
      ((1073739385 : ℝ) / 1073741824) ≤ (2147483648 : ℕ) :=
  list_bound dom 1073741824 2439 2147483648 hn (by decide) hfield (fun P L m l => by
    have h := dual_bound graph P L
    rw [m, l] at h
    exact h.trans_lt (by decide)) width

#print axioms first
#print axioms second
end ProximityGap.AffineListIncidences
