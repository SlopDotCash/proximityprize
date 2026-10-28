/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds.SubspaceDesign

/-!
# ABF26 C3.5 needs an admissible folding element

`CodingTheory.frs_list_decoding_capacity_cz25` (ABF26 Corollary 3.5, [CZ25 Cor 2.21]) is stated
for `FRS[F, L, k, s, ω]` with `ω` `(L, s)`-admissible (ABF26 Definitions 2.14 and 2.15). This
file records why the Lean statement carries that guard: without it the C3.5 inequality is false.

For `ω = 1` the folded code is the `s`-fold repetition of `RS[F, L, k]`, so its list sizes are
those of plain Reed-Solomon. Take `F = L = 𝔽₇`, `k = 2`, `s = 119`, `η = 1/8`. The C3.5 radius is
`1 - (2/7)·119/112 - 1/8 = 4/7` and the bound is `(119·5/7 + 1 - 8)/(112/8) = 39/7 < 6`. The word
`w = (0, 0, 0, 1, 1, 3, 2)` agrees with each of the six lines `0`, `2X`, `5X`, `1 + 6X`,
`5 + X`, `6 + 4X` on at least `3` of the `7` points, so `Λ(C, 4/7) ≥ 6`.

* `frs_list_decoding_capacity_cz25_body_false_omega_one`: the unguarded C3.5 inequality fails at
  this instance.
* `not_admissible_omega_one`: `ω = 1` is not admissible there, so the guarded statement makes no
  claim about it.
-/

namespace CodingTheory.CZ25FRSAdmissibilityRegime

open ListDecodable

local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The identity evaluation domain `𝔽₇ ↪ 𝔽₇`. -/
def dom7 : ZMod 7 ↪ ZMod 7 := Function.Embedding.refl (ZMod 7)

/-- Repeat each coordinate of a word across the `s` folded slots. -/
def rep (s : ℕ) (u : ZMod 7 → ZMod 7) : ZMod 7 → Fin s → ZMod 7 := fun x _ => u x

lemma rep_injective (s : ℕ) [NeZero s] : Function.Injective (rep s) := by
  intro u v h
  funext x
  exact congrFun (congrFun h x) 0

lemma hammingDist_rep (s : ℕ) [NeZero s] [DecidableEq (Fin s → ZMod 7)]
    (u v : ZMod 7 → ZMod 7) : hammingDist (rep s u) (rep s v) = hammingDist u v := by
  unfold hammingDist
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  constructor
  · intro h h'
    apply h
    funext j
    simp [rep, h']
  · intro h h'
    exact h (congrFun h' 0)

/-- The line `a + b·X` as a word on `𝔽₇`. -/
def line (a b : ZMod 7) : ZMod 7 → ZMod 7 := fun x => a + b * x

/-- With `ω = 1`, the repeated line `a + b·X` is a folded-RS codeword of degree `< 2`. -/
lemma rep_line_mem (s : ℕ) (a b : ZMod 7) :
    rep s (line a b) ∈ ReedSolomon.Folded.frsCode dom7 2 s 1 := by
  rw [ReedSolomon.Folded.mem_frsCode_iff]
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X, ?_, ?_⟩
  · rw [Polynomial.mem_degreeLT]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le b) (by norm_num)
  · intro x j
    simp [rep, line, dom7]

/-- The received word `(0, 0, 0, 1, 1, 3, 2)`. -/
def w : ZMod 7 → ZMod 7 := ![0, 0, 0, 1, 1, 3, 2]

/-- Six lines that each agree with `w` on at least three points. -/
def lines : Finset (ZMod 7 → ZMod 7) :=
  {line 0 0, line 0 2, line 0 5, line 1 6, line 5 1, line 6 4}

lemma lines_card : lines.card = 6 := by decide

set_option maxRecDepth 100000 in
lemma lines_close : ∀ u ∈ lines, hammingDist w u ≤ 4 := by
  intro u hu
  simp only [lines, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `Λ(FRS[𝔽₇, 𝔽₇, 2, 119, 1], 4/7) ≥ 6`. -/
theorem six_le_lambda :
    (6 : ℕ∞) ≤ Lambda
      (ReedSolomon.Folded.frsCode dom7 2 119 1 : Set (ZMod 7 → Fin 119 → ZMod 7)) (4 / 7) := by
  have hsub : (lines.image (rep 119) : Set (ZMod 7 → Fin 119 → ZMod 7)) ⊆
      closeCodewordsRel
        (ReedSolomon.Folded.frsCode dom7 2 119 1 : Set (ZMod 7 → Fin 119 → ZMod 7))
        (rep 119 w) (4 / 7) := by
    intro c hc
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc
    obtain ⟨u, hu, rfl⟩ := hc
    refine ⟨?_, ?_⟩
    · simp only [lines, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact rep_line_mem 119 _ _
    · simp only [relHammingBall, Set.mem_setOf_eq]
      unfold Code.relHammingDist
      rw [hammingDist_rep, ZMod.card]
      push_cast
      rw [div_le_div_iff_of_pos_right (by norm_num)]
      exact_mod_cast lines_close u hu
  refine le_trans ?_ (le_iSup _ (rep 119 w))
  have h6 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ (rep_injective 119),
    lines_card] at h6
  exact_mod_cast h6

/-- **The unguarded C3.5 inequality is false for `ω = 1`.** At `F = L = 𝔽₇`, `k = 2`, `s = 119`,
`η = 1/8`, the body of `frs_list_decoding_capacity_cz25` (without its admissibility guard) has
radius `4/7` and bound `39/7`, but the list at radius `4/7` has six codewords. -/
theorem frs_list_decoding_capacity_cz25_body_false_omega_one :
    ¬ (let n : ℝ := Fintype.card (ZMod 7)
      let ρ : ℝ := (2 : ℕ) / n
      let δ : ℝ := 1 - ρ * (119 : ℕ) / ((119 : ℕ) - 1 / (1 / 8) + 1) - 1 / 8
      let bound : ℝ := ((119 : ℕ) * (1 - ρ) + 1 - 1 / (1 / 8)) /
        (1 / 8 * ((119 : ℕ) + 1 - 1 / (1 / 8)))
      (Lambda (ReedSolomon.Folded.frsCode dom7 2 119 1 : Set (ZMod 7 → Fin 119 → ZMod 7)) δ :
          ENNReal) ≤ ENNReal.ofReal bound) := by
  intro h
  simp only [ZMod.card] at h
  have hδ : (1 : ℝ) - ((2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ) * ((119 : ℕ) : ℝ) /
      (((119 : ℕ) : ℝ) - 1 / (1 / 8) + 1) - 1 / 8 = 4 / 7 := by norm_num
  have hB : (((119 : ℕ) : ℝ) * (1 - ((2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) + 1 - 1 / (1 / 8)) /
      (1 / 8 * (((119 : ℕ) : ℝ) + 1 - 1 / (1 / 8))) = 39 / 7 := by norm_num
  rw [hδ, hB] at h
  have h6 : (6 : ENNReal) ≤ ENNReal.ofReal (39 / 7) :=
    le_trans (by exact_mod_cast six_le_lambda) h
  rw [show (6 : ENNReal) = ENNReal.ofReal 6 by simp,
    ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h6
  norm_num at h6

/-- `ω = 1` is not `(𝔽₇, 119)`-admissible: it fixes every domain point. -/
theorem not_admissible_omega_one :
    ¬ ReedSolomon.Folded.Admissible (Finset.univ.image dom7) 119 (1 : ZMod 7) := by
  intro h
  exact h.2 1 (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩) 1 (by norm_num) (by norm_num)
    (by simp)

#print axioms frs_list_decoding_capacity_cz25_body_false_omega_one
#print axioms not_admissible_omega_one

end CodingTheory.CZ25FRSAdmissibilityRegime
