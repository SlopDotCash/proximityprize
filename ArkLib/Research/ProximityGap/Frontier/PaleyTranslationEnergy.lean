/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._R17TchiMomentIdentities
import Mathlib.Combinatorics.Additive.Energy

/-!
# Paley discrepancy over translations of one set

For two fixed subsets of a finite field, the sum of squared character discrepancies over the
translations is the field size times the additive energy minus the squared number of pairs.
This bounds the number of translations with discrepancy above a given threshold.
-/

namespace ArkLib.ProximityGap.Frontier.PaleyTranslationEnergy

open Finset R17TchiMomentIdentities

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem covariance {χ : MulChar F ℂ} (hχ : χ ≠ 1) (x y : F) :
    ∑ v : F, χ (x + v) * (starRingEnd ℂ) (χ (y + v)) =
      (Fintype.card F : ℂ) * (if x = y then 1 else 0) - 1 := by
  have shift : ∑ v : F, χ (x + v) * (starRingEnd ℂ) (χ (y + v)) =
      ∑ z : F, χ z * (starRingEnd ℂ) (χ (z + (y - x))) := by
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun v => ?_)
    change _ = χ (x + v) * (starRingEnd ℂ) (χ (x + v + (y - x)))
    rw [show x + v + (y - x) = y + v by ring]
  rw [shift]
  by_cases h : x = y
  · subst y
    simpa using sum_mulChar_mul_conj_self χ
  · simpa [h] using sum_mulChar_mul_conj_shift hχ (sub_ne_zero.mpr (Ne.symm h))

/-- Exact second moment over all translations of either of two fixed sets. -/
theorem mulChar_sum_sq_translation {χ : MulChar F ℂ} (hχ : χ ≠ 1) (A B : Finset F) :
    ∑ v : F, ‖∑ a ∈ A, ∑ b ∈ B, χ (a + b + v)‖ ^ 2 =
      (Fintype.card F : ℝ) * (A.addEnergy B : ℝ) - ((A.card : ℝ) * B.card) ^ 2 := by
  classical
  let P := A ×ˢ B
  let s (x : F × F) := x.1 + x.2
  let W (v : F) := ∑ x ∈ P, χ (s x + v)
  have henergy : (A.addEnergy B : ℂ) =
      ∑ x ∈ P, ∑ y ∈ P, (if s x = s y then (1 : ℂ) else 0) := by
    rw [addEnergy_eq_card_filter, natCast_card_filter, Finset.sum_product]
  have hexpand (v : F) : ((‖W v‖ ^ 2 : ℝ) : ℂ) =
      ∑ x ∈ P, ∑ y ∈ P, χ (s x + v) * (starRingEnd ℂ) (χ (s y + v)) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [W, map_sum, Finset.sum_mul_sum]
  have hmoment : ∑ v : F, ((‖W v‖ ^ 2 : ℝ) : ℂ) =
      (Fintype.card F : ℂ) * (A.addEnergy B : ℂ) - ((A.card : ℂ) * B.card) ^ 2 := by
    simp_rw [hexpand, Finset.sum_comm (s := Finset.univ) (t := P), covariance hχ]
    simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← henergy]
    simp [P, nsmul_eq_mul, pow_two]
  have hreal : ∑ v : F, ‖W v‖ ^ 2 =
      (Fintype.card F : ℝ) * (A.addEnergy B : ℝ) - ((A.card : ℝ) * B.card) ^ 2 := by
    exact_mod_cast hmoment
  simpa only [W, P, s, Finset.sum_product] using hreal

/-- The translations at which the discrepancy reaches the specified threshold. -/
noncomputable def exceptions (χ : MulChar F ℂ) (A B : Finset F) (T : ℝ) : Finset F :=
  univ.filter fun v => T ≤ ‖∑ a ∈ A, ∑ b ∈ B, χ (a + b + v)‖

/-- Each exceptional translation spends at least the squared threshold in the second moment. -/
theorem exceptions_card_mul_sq_le {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (A B : Finset F) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptions χ A B T).card : ℝ) * T ^ 2 ≤
      (Fintype.card F : ℝ) * (A.addEnergy B : ℝ) - ((A.card : ℝ) * B.card) ^ 2 := by
  classical
  let W (v : F) := ‖∑ a ∈ A, ∑ b ∈ B, χ (a + b + v)‖
  calc
    _ = ∑ _ ∈ exceptions χ A B T, T ^ 2 := by simp
    _ ≤ ∑ v ∈ exceptions χ A B T, W v ^ 2 := by
      refine Finset.sum_le_sum fun v hv => ?_
      exact pow_le_pow_left₀ hT (Finset.mem_filter.mp hv).2 2
    _ ≤ ∑ v : F, W v ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ = _ := mulChar_sum_sq_translation hχ A B

private theorem energy_le_card_left (A B : Finset F) :
    A.addEnergy B ≤ A.card * B.card * A.card := by
  classical
  let P := A ×ˢ B
  let s (x : F × F) := x.1 + x.2
  let r (z : F) := (P.filter (fun x => s x = z)).card
  have hr (z : F) : r z ≤ A.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · exact fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
    · rintro ⟨a, b⟩ hx ⟨a', b'⟩ hy h
      change a = a' at h
      subst a'
      have he := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact Prod.ext rfl (add_left_cancel (show a + b = a + b' from he))
  have hsum : ∑ z : F, r z = A.card * B.card := by
    simpa [r, P] using (sum_card_fiberwise_eq_card_filter P univ s)
  calc
    A.addEnergy B = ∑ z : F, r z ^ 2 := addEnergy_eq_sum_sq _ _
    _ ≤ ∑ z : F, r z * A.card := by
      exact sum_le_sum fun z _ => by rw [pow_two]; gcongr; exact hr z
    _ = _ := by rw [← sum_mul, hsum]

/-- At most the smaller set size many pairs represent any one sum. -/
theorem addEnergy_le_card_mul_min (A B : Finset F) :
    A.addEnergy B ≤ A.card * B.card * min A.card B.card := by
  rcases le_total A.card B.card with h | h
  · simpa only [min_eq_left h] using energy_le_card_left A B
  · rw [min_eq_right h, addEnergy_comm, mul_comm A.card B.card]
    exact energy_le_card_left B A

/-- A size-only bound on exceptional translations, valid for arbitrary sets. -/
theorem exceptions_card_mul_sq_le_card_mul_min {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (A B : Finset F) {T : ℝ} (hT : 0 ≤ T) :
    ((exceptions χ A B T).card : ℝ) * T ^ 2 ≤
      (Fintype.card F : ℝ) * ((A.card : ℝ) * B.card * min A.card B.card) -
        ((A.card : ℝ) * B.card) ^ 2 := by
  have h := addEnergy_le_card_mul_min A B
  refine (exceptions_card_mul_sq_le hχ A B hT).trans ?_
  gcongr
  exact_mod_cast h

/-- At relative threshold `η`, the fraction of exceptional translations is at most
`(1 / max(|A|, |B|) − 1 / q) / η²` when `η > 0`. The product form includes `η = 0`. -/
theorem relative_exceptions_card_mul_le {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {A B : Finset F} (hA : A.Nonempty) (hB : B.Nonempty) {η : ℝ} (hη : 0 ≤ η) :
    ((exceptions χ A B (η * ((A.card : ℝ) * B.card))).card : ℝ) * η ^ 2 *
        max A.card B.card ≤ (Fintype.card F : ℝ) - max A.card B.card := by
  let m : ℝ := (min A.card B.card : ℕ)
  let M : ℝ := (max A.card B.card : ℕ)
  let q : ℝ := Fintype.card F
  let T := η * ((A.card : ℝ) * B.card)
  let N : ℝ := (exceptions χ A B T).card
  have hm : 0 < m := by dsimp [m]; exact_mod_cast lt_min hA.card_pos hB.card_pos
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (hA.card_pos.trans_le (le_max_left A.card B.card))
  have hprod : m * M = (A.card : ℝ) * B.card := by
    dsimp [m, M]
    exact_mod_cast min_mul_max A.card B.card
  have h := exceptions_card_mul_sq_le_card_mul_min hχ A B
    (show 0 ≤ T by dsimp [T]; positivity)
  change N * (η * ((A.card : ℝ) * B.card)) ^ 2 ≤
    q * (((A.card : ℝ) * B.card) * m) - ((A.card : ℝ) * B.card) ^ 2 at h
  rw [← hprod] at h
  change N * η ^ 2 * M ≤ q - M
  apply le_of_mul_le_mul_left (a := m ^ 2 * M) _ (by positivity)
  calc
    _ = N * (η * (m * M)) ^ 2 := by ring
    _ ≤ _ := h
    _ = _ := by ring

end ArkLib.ProximityGap.Frontier.PaleyTranslationEnergy

#print axioms ArkLib.ProximityGap.Frontier.PaleyTranslationEnergy.mulChar_sum_sq_translation
#print axioms
  ArkLib.ProximityGap.Frontier.PaleyTranslationEnergy.exceptions_card_mul_sq_le_card_mul_min
#print axioms ArkLib.ProximityGap.Frontier.PaleyTranslationEnergy.relative_exceptions_card_mul_le
