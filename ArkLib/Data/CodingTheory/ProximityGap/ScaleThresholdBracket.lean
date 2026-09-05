/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListThresholdWellDefined
import ArkLib.Data.CodingTheory.ProximityGap.ScaleJohnsonInstance
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT1

/-!
# Issue #232 — THE PRIZE THRESHOLD OBJECT, BRACKETED, for in-tree Reed–Solomon at prize scale

The capstone composition.  `ListThresholdWellDefined` made the prize's `δ*` a first-class object
(`aStar`, with the crossing API); `PrizeScaleJohnsonInstance` bounds lists at prize scale; Round-5's
`exists_interior_list_ge_unconditional` violates budgets near capacity.  This file composes all
three **for the genuine in-tree `ReedSolomon.code`** at the prize's own configuration
(`n = 2²⁰`, `ρ = 1/2`, `|F| ≤ 2²⁵⁶`):

* `maxList_rs_le_91` — the worst-case list of the RS code at agreement `750000` is `≤ 91`
  (each listed codeword pulls back to its unique degree-`< 2¹⁹` polynomial; the prize-scale GS
  instance caps the polynomial list).
* `ninetyone_lt_maxList_rs` — at agreement `2¹⁹ + 1` (just inside capacity) the worst-case list
  **exceeds 91**: the Round-5 averaging word has `≥ C(2²⁰, 2¹⁹+1)/q` close codewords, and the
  central-binomial chain gives `C(2²⁰, 2¹⁹+1) > 2²⁶³ > 91·q` for every `q ≤ 2²⁵⁶`.
* `prize_threshold_bracket` (HEADLINE) — therefore the **threshold object itself** satisfies

  `2¹⁹ + 1  <  aStar(RS, 91)  ≤  750000`,

  i.e. the prize's `δ*` (at budget 91, in agreement form) is machine-checked to lie in the window
  `δ* ∈ [1 − 750000/2²⁰, 1 − (2¹⁹+1)/2²⁰) ≈ [0.2848, 0.5)` — confined between 1.2% inside the
  Johnson radius and the capacity edge, for the actual in-tree Reed–Solomon code at full prize
  scale.  Sharpening this window (in particular its position relative to Johnson `≈ 0.2929`) is
  exactly the open content of the prize.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset Polynomial

namespace ArkLib.CodingTheory.PrizeScaleThresholdBracket

open ArkLib.CodingTheory.ListThresholdWellDefined
open ArkLib.CodingTheory.Round5Unconditional
open ArkLib.CodingTheory.Round4InteriorList

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The in-tree Reed–Solomon code at prize scale (`n = 2²⁰`, degree `< 2¹⁹`), as a `Finset` of
words (the carrier for the `maxList`/`aStar` machinery). -/
noncomputable def rsCodeF (D : Fin (2 ^ 20) ↪ F) : Finset (Fin (2 ^ 20) → F) := by
    classical
    exact Finset.univ.filter (· ∈ ReedSolomon.code D (2 ^ 19))

/-- The two agreement counts in play (`ListThresholdWellDefined.agree` and the Round-4/5
`agreeCount`) are the same number — the underlying filters differ only in their `Decidable`
instances. -/
theorem agree_eq_agreeCount (c w : Fin (2 ^ 20) → F) :
    agree c w = agreeCount c w := by
  unfold agree agreeCount
  exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)

set_option linter.constructorNameAsVariable false

/-- Generic-`n` form of "each word's filtered list is at most the worst case". Proved with `n` a
variable and only then instantiated at `2 ^ 20`: elaborating the `Finset.le_sup` unification with
the literal in the type forces a defeq descent into `Finset.univ` over `Fin (2 ^ 20)` (a
`finRange`-scale whnf), which does not terminate in practice. -/
theorem filter_card_le_maxList {n : ℕ} (C : Finset (Fin n → F)) (a : ℕ) (w : Fin n → F) :
    (C.filter fun c => a ≤ agree c w).card ≤ maxList C a := by
  unfold maxList
  exact Finset.le_sup (f := fun w => (C.filter fun c => a ≤ agree c w).card)
    (Finset.mem_univ w)


/-- **Upper side: the RS worst-case list at agreement `750000` is `≤ 91`.**  Every listed codeword
is the evaluation of a unique degree-`< 2¹⁹` polynomial; the polynomial pullback of the list is
admissible for `prize_scale_johnson_list_bound`, which caps it at `91`. -/
theorem maxList_rs_le_91 (D : Fin (2 ^ 20) ↪ F) :
    maxList (rsCodeF D) 750000 ≤ 91 := by
  classical
  apply Finset.sup_le
  intro w _
  set S := (rsCodeF D).filter (fun c => 750000 ≤ agree c w) with hS
  clear_value S
  -- choose, for each listed word, its polynomial
  have hpoly : ∀ v ∈ S, ∃ p : F[X], p.degree < (2 ^ 19 : ℕ) ∧ v = ReedSolomon.evalOnPoints D p := by
    intro v hv
    rw [hS, Finset.mem_filter] at hv
    obtain ⟨hv1, hv2⟩ := hv
    have hcode : v ∈ ReedSolomon.code D (2 ^ 19) := by
      rw [rsCodeF, Finset.mem_filter] at hv1
      obtain ⟨-, h⟩ := hv1
      exact h
    exact ReedSolomon.mem_code_iff_exists_polynomial.mp hcode
  set L : Finset F[X] := S.attach.image
    (fun v => Classical.choose (hpoly v.val v.property)) with hL
  clear_value L
  -- the pullback has the same cardinality (evaluation determines the word)
  have hcardL : S.card = L.card := by
    rw [hL]
    rw [Finset.card_image_of_injOn, Finset.card_attach]
    intro v₁ _ v₂ _ heq
    have h₁ := (Classical.choose_spec (hpoly v₁.1 v₁.2)).2
    have h₂ := (Classical.choose_spec (hpoly v₂.1 v₂.2)).2
    apply Subtype.ext
    have heq' : Classical.choose (hpoly v₁.1 v₁.2) = Classical.choose (hpoly v₂.1 v₂.2) := by
      simpa using heq
    rw [h₁, h₂, heq']
  -- the pullback is admissible for the prize-scale GS bound
  have hbound : L.card ≤ 91 := by
    apply ArkLib.CodingTheory.PrizeScaleJohnson.prize_scale_johnson_list_bound
      (⇑D) w D.injective L
    · -- degrees
      intro f hf
      simp only [hL, Finset.mem_image] at hf
      obtain ⟨v, _, rfl⟩ := hf
      have hdeg := (Classical.choose_spec (hpoly v.1 v.2)).1
      rcases eq_or_ne (Classical.choose (hpoly v.1 v.2)) 0 with h0 | h0
      · rw [h0]
        simp
      · have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hdeg)
        omega
    · -- agreements
      intro f hf
      simp only [hL, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hf
      obtain ⟨vv, hvS, rfl⟩ := hf
      have heval := (Classical.choose_spec (hpoly vv hvS)).2
      have hagree : 750000 ≤ agree vv w := by
        have h' := hvS
        rw [hS, Finset.mem_filter] at h'
        obtain ⟨-, h⟩ := h'
        exact h
      calc 750000 ≤ agree vv w := hagree
        _ = (Finset.univ.filter fun s : Fin (2 ^ 20) =>
              (Classical.choose (hpoly vv hvS)).eval (D s) = w s).card := by
            unfold agree
            refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
            conv_lhs => rw [heval]
            exact Iff.rfl
  omega

/-- **The central-binomial chain:** `91·q < C(2²⁰, 2¹⁹+1)` for every `q ≤ 2²⁵⁶` — symbolic
(`4^(2¹⁹) = 2^(2²⁰)` dwarfs everything), no astronomical computation. -/
theorem ninetyone_mul_q_lt_choose (q : ℕ) (hq : q ≤ 2 ^ 256) :
    91 * q < (2 ^ 20).choose (2 ^ 19 + 1) := by
  -- Generalize the two binomial coefficients to opaque variables immediately: `Nat.choose` on
  -- million-scale literals must never reach a kernel-side whnf (no GMP fast path; evaluating
  -- `choose 2^20 2^19` is astronomically expensive), so every arithmetic step below works with
  -- plain fvars `C`, `C'` and only the defining equations mention `choose`.
  obtain ⟨C, hC⟩ : ∃ x, ((2 : ℕ) ^ 20).choose (2 ^ 19) = x := ⟨_, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ x, ((2 : ℕ) ^ 20).choose (2 ^ 19 + 1) = x := ⟨_, rfl⟩
  rw [hC']
  -- 2·C(k+1) ≥ C(k):  C(k+1)·(k+1) = C(k)·(n−k) = C(k)·2¹⁹  and  2·(2¹⁹+1) ≥ 2²⁰ ≥ 2¹⁹.
  have h := Nat.choose_succ_right_eq (2 ^ 20) (2 ^ 19)
  rw [hC, hC', show (2 : ℕ) ^ 20 - 2 ^ 19 = 2 ^ 19 by norm_num] at h
  -- h : C' * (2^19 + 1) = C * 2^19
  have hratio : C ≤ 2 * C' := by
    have h1 : C * 2 ^ 19 ≤ (2 * C') * 2 ^ 19 := by
      calc C * 2 ^ 19 = C' * (2 ^ 19 + 1) := h.symm
        _ ≤ C' * 2 ^ 20 := by gcongr; norm_num
        _ = (2 * C') * 2 ^ 19 := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by norm_num)
  -- 4^(2¹⁹) ≤ 2²⁰ · C  (central binomial)
  have hcb : 4 ^ (2 ^ 19) ≤ 2 ^ 20 * C := by
    have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom (2 ^ 19) (by norm_num)
    have hcb_eq : Nat.centralBinom (2 ^ 19) = C := by
      rw [← hC, Nat.centralBinom]
      norm_num
    rw [hcb_eq] at h4
    calc 4 ^ (2 ^ 19) ≤ 2 * 2 ^ 19 * C := h4
      _ = 2 ^ 20 * C := by ring
  -- 4^(2¹⁹) = 2^(2²⁰)
  have hfour : (4 : ℕ) ^ (2 ^ 19) = 2 ^ (2 ^ 20) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    norm_num
  -- chain: 2²⁸⁴ < 2^(2²⁰) ≤ 2²⁰·C ≤ 2²¹·C'  ⟹  2²⁶³ < C'
  have hbig : (2 : ℕ) ^ 284 < 2 ^ 21 * C' := by
    calc (2 : ℕ) ^ 284 < 2 ^ (2 ^ 20) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
      _ = 4 ^ (2 ^ 19) := hfour.symm
      _ ≤ 2 ^ 20 * C := hcb
      _ ≤ 2 ^ 20 * (2 * C') := by gcongr
      _ = 2 ^ 21 * C' := by ring
  have hCbig : (2 : ℕ) ^ 263 < C' := by
    have h284 : (2 : ℕ) ^ 284 = 2 ^ 21 * 2 ^ 263 := by rw [← pow_add]
    rw [h284] at hbig
    exact Nat.lt_of_mul_lt_mul_left hbig
  calc 91 * q ≤ 91 * 2 ^ 256 := by gcongr
    _ < 2 ^ 7 * 2 ^ 256 := by gcongr <;> norm_num
    _ = 2 ^ 263 := by rw [← pow_add]
    _ < C' := hCbig

-- Keep the dimension symbolic while constructing and checking the counting proof.
open scoped Classical in
private theorem choose_le_card_mul_maxList_generic {n k : ℕ} (D : Fin n ↪ F)
    (hk : 0 < k) (hkn : k ≤ n) (hint : (k + 1) ^ 2 < k * n) :
    n.choose (k + 1) ≤ Fintype.card F *
      maxList (Finset.univ.filter (fun v : Fin n → F => v ∈ ReedSolomon.code D k))
        (k + 1) := by
  classical
  obtain ⟨g, _hgdeg, hcount⟩ :=
    exists_interior_list_ge_unconditional (ι := Fin n) D hk
      (by simpa only [Fintype.card_fin] using hkn) Fintype.card_pos
      (by simpa only [Fintype.card_fin] using hint)
  rw [Fintype.card_fin] at hcount
  let w : Fin n → F := fun i => g.eval (D i)
  have hagree (v : Fin n → F) : agree v w = agreeCount v w := by
    unfold agree agreeCount
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  have hsame : (Finset.univ.filter (fun v : Fin n → F =>
      v ∈ ReedSolomon.code D k ∧ k + 1 ≤ agreeCount v w)).card =
      ((Finset.univ.filter (fun v : Fin n → F => v ∈ ReedSolomon.code D k)).filter
        (fun v => k + 1 ≤ agree v w)).card := by
    refine congrArg Finset.card ?_
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun v _ => by rw [hagree]
  rw [hsame] at hcount
  exact le_trans hcount (Nat.mul_le_mul_left (Fintype.card F)
    (filter_card_le_maxList _ (k + 1) w))

/-- **Lower side: at agreement `2¹⁹ + 1` the RS worst-case list EXCEEDS 91** (for any prize-scale
field `q ≤ 2²⁵⁶`): the Round-5 averaging word has `≥ C(2²⁰, 2¹⁹+1)/q > 91` close codewords. -/
theorem ninetyone_lt_maxList_rs (D : Fin (2 ^ 20) ↪ F)
    (hq : Fintype.card F ≤ 2 ^ 256) :
    91 < maxList (rsCodeF D) (2 ^ 19 + 1) := by
  classical
  have hcount := choose_le_card_mul_maxList_generic (k := 2 ^ 19) D
    (by norm_num) (by norm_num) (by norm_num)
  have hchain : Fintype.card F * 91 <
      Fintype.card F * maxList (rsCodeF D) (2 ^ 19 + 1) := by
    calc Fintype.card F * 91 = 91 * Fintype.card F := Nat.mul_comm _ _
      _ < (2 ^ 20).choose (2 ^ 19 + 1) := ninetyone_mul_q_lt_choose _ hq
      _ ≤ Fintype.card F * maxList (rsCodeF D) (2 ^ 19 + 1) := hcount
  exact Nat.lt_of_mul_lt_mul_left hchain

/-- **HEADLINE — THE PRIZE THRESHOLD OBJECT, BRACKETED.**  For the in-tree Reed–Solomon code at
the prize's own configuration (`n = 2²⁰`, rate `1/2`, any field with `|F| ≤ 2²⁵⁶`), the threshold
object itself satisfies

  `2¹⁹ + 1  <  aStar(RS, 91)  ≤  750000`,

i.e. the agreement threshold at budget `91` is confined between the capacity edge and a point
1.2% inside the Johnson radius — `δ* ∈ [0.2848, 0.5)` for the genuine code at full prize scale.
Sharpening this window is exactly the open content of the prize. -/
theorem prize_threshold_bracket (D : Fin (2 ^ 20) ↪ F)
    (hq : Fintype.card F ≤ 2 ^ 256) :
    2 ^ 19 + 1 < aStar (rsCodeF D) 91 (by norm_num) ∧
    aStar (rsCodeF D) 91 (by norm_num) ≤ 750000 :=
  aStar_mem_window (rsCodeF D) 91 (by norm_num)
    (maxList_rs_le_91 D) (ninetyone_lt_maxList_rs D hq)

end ArkLib.CodingTheory.PrizeScaleThresholdBracket

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.maxList_rs_le_91
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.ninetyone_mul_q_lt_choose
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.ninetyone_lt_maxList_rs
#print axioms ArkLib.CodingTheory.PrizeScaleThresholdBracket.prize_threshold_bracket
