/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityLeaves2
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.IsPrimePow
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# JH01 List-Decoding Separation Helpers

Small Reed-Solomon facts used by the JH01 list-size separation route.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory
namespace ReedSolomon

variable {F : Type} [Field F]

/-- A Reed-Solomon code of degree bound `j` evaluated on `j + 1` points is a
proper submodule of the full word space, hence some word is not a codeword. -/
theorem exists_word_not_mem_code_of_length_succ (j : ℕ) (domain : Fin (j + 1) ↪ F) :
    ∃ w : Fin (j + 1) → F, w ∉ ReedSolomon.code domain j := by
  have hdim : Module.finrank F (ReedSolomon.code domain j) = j := by
    have h : j ≤ Fintype.card (Fin (j + 1)) := by simp
    simpa [LinearCode.dim] using ReedSolomon.dim_eq_deg_of_le' (α := domain) h
  have hne : ReedSolomon.code domain j ≠ ⊤ := by
    intro htop
    have : Module.finrank F (ReedSolomon.code domain j) = j + 1 := by
      rw [htop]
      simp
    omega
  by_contra hmiss
  push Not at hmiss
  apply hne
  refine le_antisymm le_top ?_
  intro w _
  exact hmiss w

/-- For any target word on `j + 1` evaluation points and any excluded point
`x`, there is a degree-`< j` Reed-Solomon codeword agreeing with the target off
`x`. This is the interpolation step used in the JH01 list-size separation. -/
theorem exists_codeword_agree_off_point (j : ℕ) (domain : Fin (j + 1) ↪ F)
    (w : Fin (j + 1) → F) (x : Fin (j + 1)) :
    ∃ c ∈ ReedSolomon.code domain j, ∀ i, i ≠ x → c i = w i := by
  classical
  set S : Finset (Fin (j + 1)) := Finset.univ.filter (fun i => i ≠ x) with hS
  have hScard : S.card ≤ j := by
    have : S.card = j := by
      rw [hS, Finset.filter_ne']
      simp
    omega
  obtain ⟨c, hc_mem, hc_agree⟩ :=
    ReedSolomon.ReedSolomon_interpolate_through_subset (k := j) domain S hScard w
  refine ⟨c, hc_mem, ?_⟩
  intro i hi
  apply hc_agree
  rw [hS]
  simp [hi]

/-- If two words on `j + 1` positions agree away from one point, then they are
within relative Hamming radius `1 / (j + 1)`. -/
theorem mem_relHammingBall_of_agree_off_point (j : ℕ) (w c : Fin (j + 1) → F)
    (x : Fin (j + 1)) (hagree : ∀ i, i ≠ x → c i = w i) :
    c ∈ _root_.ListDecodable.relHammingBall w (1 / (j + 1 : ℝ)) := by
  classical
  have hn_pos : 0 < Fintype.card (Fin (j + 1)) := Fintype.card_pos
  have hdist : hammingDist w c ≤ 1 := by
    have hfsub : Finset.univ.filter (fun i => w i ≠ c i) ⊆ {x} := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hix
      simp only [Finset.mem_singleton] at hix
      exact hi ((hagree i hix).symm)
    have heq : hammingDist w c = (Finset.univ.filter (fun i => w i ≠ c i)).card := by
      rw [hammingDist]
    rw [heq]
    calc (Finset.univ.filter (fun i => w i ≠ c i)).card
        ≤ ({x} : Finset (Fin (j + 1))).card := Finset.card_le_card hfsub
      _ = 1 := Finset.card_singleton x
  simp only [_root_.ListDecodable.relHammingBall, Set.mem_setOf_eq, Code.relHammingDist,
    NNRat.cast_div, NNRat.cast_natCast]
  rw [div_le_iff₀ (by exact_mod_cast hn_pos :
    (0 : ℝ) < (Fintype.card (Fin (j + 1)) : ℝ))]
  have hn : (Fintype.card (Fin (j + 1)) : ℝ) = (j : ℝ) + 1 := by simp
  rw [hn]
  have hd : (hammingDist w c : ℝ) ≤ 1 := by exact_mod_cast hdist
  have hcancel : (1 / (j + 1 : ℝ)) * ((j : ℝ) + 1) = 1 := by
    field_simp
  rw [hcancel]
  exact hd

/-- Generalized combinatorial core of JH01 / ABF26 Theorem 3.14.  For any index type `ι`
of size `j + 1` and any evaluation domain `domain : ι ↪ F`, the Reed-Solomon code
`RS[F, domain, j]` is not uniquely decodable at relative radius `1 / (j + 1)`: some word has
more than `j` close codewords. -/
theorem exists_word_with_many_close_codewords_of_card_succ
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    (j : ℕ) (hcard_ι : Fintype.card ι = j + 1) (domain : ι ↪ F) :
    ∃ w : ι → F,
      (j : ℕ∞) <
        (_root_.ListDecodable.closeCodewordsRel ((ReedSolomon.code domain j : Set (ι → F)))
          w (1 / (j + 1 : ℝ))).ncard := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ι → F, w ∉ ReedSolomon.code domain j := by
    have hdim : Module.finrank F (ReedSolomon.code domain j) = j := by
      have h : j ≤ Fintype.card ι := by omega
      simpa [LinearCode.dim] using ReedSolomon.dim_eq_deg_of_le' (α := domain) h
    have hfull : Module.finrank F (ι → F) = j + 1 := by
      rw [Module.finrank_fintype_fun_eq_card, hcard_ι]
    have hne : ReedSolomon.code domain j ≠ ⊤ := by
      intro htop
      have : Module.finrank F (ReedSolomon.code domain j) = j + 1 := by
        rw [htop]
        simp [hfull]
      omega
    by_contra hmiss
    push Not at hmiss
    exact hne (le_antisymm le_top (fun x _ => hmiss x))
  refine ⟨w, ?_⟩
  have hstep2 : ∀ x : ι,
      ∃ c ∈ ReedSolomon.code domain j, ∀ i, i ≠ x → c i = w i := by
    intro x
    set S : Finset ι := Finset.univ.filter (fun i => i ≠ x) with hS
    have hScard : S.card ≤ j := by
      have hSc : S.card = j := by
        rw [hS, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ x),
          Finset.card_univ, hcard_ι]
        omega
      omega
    obtain ⟨c, hc_mem, hc_agree⟩ :=
      ReedSolomon.ReedSolomon_interpolate_through_subset (k := j) domain S hScard w
    exact ⟨c, hc_mem, fun i hi => hc_agree i (by rw [hS]; simp [hi])⟩
  choose cwf hcw_mem hcw_agree using hstep2
  have hinj : Function.Injective cwf := by
    intro x y hxy
    by_contra hne
    apply hw
    have hagree_all : ∀ i, cwf x i = w i := by
      intro i
      by_cases hix : i = x
      · have hiy : i ≠ y := by rw [hix]; exact hne
        have hval : cwf y i = w i := hcw_agree y i hiy
        rw [hxy]
        exact hval
      · exact hcw_agree x i hix
    have hcwx : cwf x = w := funext hagree_all
    rw [← hcwx]
    exact hcw_mem x
  have hclose : ∀ x, cwf x ∈
      _root_.ListDecodable.closeCodewordsRel ((ReedSolomon.code domain j : Set (ι → F)))
        w (1 / (j + 1 : ℝ)) := by
    intro x
    refine ⟨hcw_mem x, ?_⟩
    have hdist : hammingDist w (cwf x) ≤ 1 := by
      have hfsub : Finset.univ.filter (fun i => w i ≠ cwf x i) ⊆ {x} := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hix
        simp only [Finset.mem_singleton] at hix
        exact hi ((hcw_agree x i hix).symm)
      have heq : hammingDist w (cwf x)
          = (Finset.univ.filter (fun i => w i ≠ cwf x i)).card := rfl
      rw [heq]
      calc (Finset.univ.filter (fun i => w i ≠ cwf x i)).card
          ≤ ({x} : Finset ι).card := Finset.card_le_card hfsub
        _ = 1 := Finset.card_singleton x
    have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
    simp only [_root_.ListDecodable.relHammingBall, Set.mem_setOf_eq, Code.relHammingDist,
      NNRat.cast_div, NNRat.cast_natCast]
    rw [div_le_iff₀ (by exact_mod_cast hn_pos : (0 : ℝ) < (Fintype.card ι : ℝ))]
    have hn : (Fintype.card ι : ℝ) = (j : ℝ) + 1 := by rw [hcard_ι]; push_cast; ring
    rw [hn]
    have hd : (hammingDist w (cwf x) : ℝ) ≤ 1 := by exact_mod_cast hdist
    have hcancel : (1 / (j + 1 : ℝ)) * ((j : ℝ) + 1) = 1 := by field_simp
    rw [hcancel]
    convert hd using 2
  have hsub : (↑(Finset.univ.image cwf) : Set (ι → F))
      ⊆ _root_.ListDecodable.closeCodewordsRel ((ReedSolomon.code domain j : Set (ι → F)))
          w (1 / (j + 1 : ℝ)) := by
    intro c hc
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ, true_and] at hc
    obtain ⟨x, rfl⟩ := hc
    exact hclose x
  have hcardimg : (↑(Finset.univ.image cwf) : Set (ι → F)).ncard = j + 1 := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard_ι]
  have hfin : (_root_.ListDecodable.closeCodewordsRel ((ReedSolomon.code domain j : Set (ι → F)))
      w (1 / (j + 1 : ℝ))).Finite := Set.toFinite _
  have hle : j + 1 ≤
      (_root_.ListDecodable.closeCodewordsRel ((ReedSolomon.code domain j : Set (ι → F)))
        w (1 / (j + 1 : ℝ))).ncard := by
    have hmono := Set.ncard_le_ncard hsub hfin
    omega
  calc (j : ℕ∞) < ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self j
    _ ≤ _ := by exact_mod_cast hle

/-- ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every
`j ≥ 2`, infinitely many prime-power field sizes admit Reed-Solomon codes of length `j + 1`
with a received word whose relative-radius `1 / (j + 1)` list has size greater than `j`.

The statement intentionally asserts the list-size separation, not the false stronger claim
that the whole Reed-Solomon code has only `j + 1` codewords. -/
theorem rs_lambda_high_rate_jh01 (j : ℕ) (_hj_ge : 2 ≤ j) :
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let C := ReedSolomon.code domain j
            (j : ℕ∞) <
              (_root_.ListDecodable.closeCodewordsRel ((C : Set (ι → F)))
                w (1 / (j + 1 : ℝ))).ncard := by
  classical
  refine ⟨fun i => 2 ^ (i + (j + 1)), ?_, ?_, ?_⟩
  · intro a b hab
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · intro i
    exact Nat.prime_two.isPrimePow.pow (by omega)
  · intro i ι _ _ _ F _ _ _ hcardF hcardι
    have hle : Fintype.card ι ≤ Fintype.card F := by
      rw [hcardF, hcardι]
      calc j + 1 ≤ 2 ^ (j + 1) := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ (i + (j + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨domain⟩ := Function.Embedding.nonempty_of_card_le hle
    obtain ⟨w, hwsep⟩ :=
      exists_word_with_many_close_codewords_of_card_succ (ι := ι) (F := F) j hcardι domain
    exact ⟨domain, w, hwsep⟩

end ReedSolomon
end CodingTheory
