/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.BudgetTwoSixteenLower
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! # Paley discrepancy on two cosets of a single coding domain

On the order-sixteen budget-two domain, dilation by 122764 gives a complete Paley
bipartite graph. Dilation by six gives a balanced bipartite graph. Every row is a
permutation of the row at one, since every element of the coding domain is a square.
-/

namespace ProximityGap.PaleyCodingCosets

open BudgetTwoSixteen (K g domain)
open QuarterBudgetTwoThreshold (p)
open ArkLib.ProximityGap.BinaryPower (binaryPow binaryPow_eq_pow)

set_option maxRecDepth 10000

private def eulerSign (x : K) : ℤ :=
  if x = 0 then 0 else if binaryPow x (p / 2) = 1 then 1 else -1

private theorem eulerSign_eq (x : K) : eulerSign x = quadraticChar K x := by
  by_cases hx : x = 0
  · simp [eulerSign, hx]
  · have hchar : ringChar K ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
    simp only [eulerSign, hx, ↓reduceIte, binaryPow_eq_pow,
      quadraticChar_eq_pow_of_char_ne_two hchar hx, ZMod.card]

private theorem chi_domain (i : Fin 16) : quadraticChar K (domain i) = 1 := by
  have hg : quadraticChar K g = 1 := by rw [← eulerSign_eq]; decide
  change quadraticChar K (g ^ i.val) = 1
  rw [map_pow, hg, one_pow]

private theorem domain_add : ∀ i j : Fin 16, domain (i + j) = domain i * domain j := by
  decide

private theorem row_eq (c : K) (i : Fin 16) :
    ∑ j : Fin 16, quadraticChar K (domain i - c * domain j) =
      ∑ j : Fin 16, quadraticChar K (1 - c * domain j) := by
  rw [← (Equiv.addLeft i).bijective.sum_comp
    (fun j : Fin 16 => quadraticChar K (domain i - c * domain j))]
  apply Finset.sum_congr rfl
  intro j _
  change quadraticChar K (domain i - c * domain (i + j)) = _
  rw [domain_add, show domain i - c * (domain i * domain j) =
    domain i * (1 - c * domain j) by ring, map_mul, chi_domain, one_mul]

private theorem complete_signs : ∀ j : Fin 16, eulerSign (1 - 122764 * domain j) = 1 := by
  decide

private theorem balanced_sign_sum :
    (List.ofFn fun j : Fin 16 => eulerSign (1 - 6 * domain j)).sum = 0 := by
  decide

/-- Every cross difference to the coset 122764H is a nonzero square. -/
theorem complete_edges (i j : Fin 16) : quadraticChar K (domain i - 122764 * domain j) = 1 := by
  obtain ⟨k, hk⟩ := (Equiv.addLeft i).surjective j
  change i + k = j at hk
  rw [← hk, domain_add, show domain i - 122764 * (domain i * domain k) =
    domain i * (1 - 122764 * domain k) by ring, map_mul, chi_domain, one_mul,
    ← eulerSign_eq, complete_signs]

/-- Each vertex sees signed discrepancy zero across the coset 6H. -/
theorem balanced_row (i : Fin 16) :
    ∑ j : Fin 16, quadraticChar K (domain i - 6 * domain j) = 0 := by
  rw [row_eq]
  simpa only [List.sum_ofFn, eulerSign_eq] using balanced_sign_sum

/-- Both cosets are disjoint from the coding domain. -/
theorem cosets_disjoint : ∀ i j : Fin 16,
    domain i ≠ 122764 * domain j ∧ domain i ≠ 6 * domain j := by decide

/-- The complete and balanced cosets have signed discrepancies 256 and 0, respectively. -/
theorem coset_discrepancies :
    (∑ i : Fin 16, ∑ j : Fin 16, quadraticChar K (domain i - 122764 * domain j)) = 256 ∧
    (∑ i : Fin 16, ∑ j : Fin 16, quadraticChar K (domain i - 6 * domain j)) = 0 := by
  constructor
  · simp only [complete_edges, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · simp only [balanced_row, Finset.sum_const_zero]

open Polynomial

/-- A nonzero dilation of every evaluation point preserves the indexed Reed–Solomon
code as a submodule, in every dimension. -/
theorem code_eq_of_dilation {F I : Type*} [Field F] (D E : I ↪ F) (a : Fˣ)
    (he : ∀ i, E i = (a : F) * D i) (k : ℕ) :
    ReedSolomon.code E k = ReedSolomon.code D k := by
  have lift (U V : I ↪ F) (u : Fˣ) (hu : ∀ i, U i = (u : F) * V i) :
      ReedSolomon.code U k ≤ ReedSolomon.code V k := by
    rintro w hw
    obtain ⟨P, hP, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hw
    apply ReedSolomon.mem_code_iff_eval.mpr
    have hd : (C (u : F) * X).degree = 1 := degree_C_mul_X u.ne_zero
    refine ⟨P.comp (C (u : F) * X), ?_, ?_⟩
    · rwa [degree_comp (by rw [hd]; decide), hd, mul_one]
    · intro i
      rw [eval_comp, eval_mul, eval_C, eval_X, ← hu i]
      exact heval i
  apply le_antisymm (lift E D a he) (lift D E a⁻¹ _)
  intro i
  rw [he i, ← mul_assoc, Units.inv_mul, one_mul]

/-- The scaled evaluation sites retain their original power ordering. -/
def cosetDomain (c : K) (hc : c ≠ 0) : Fin 16 ↪ K :=
  domain.trans (Equiv.mulLeft₀ c hc).toEmbedding

/-- The complete and balanced cosets have the very same indexed code as the original
sixteen coordinates, hence the coding inputs have identical support-rank profiles. -/
theorem coset_codes (k : ℕ) :
    ReedSolomon.code (cosetDomain 122764 (by decide)) k = ReedSolomon.code domain k ∧
    ReedSolomon.code (cosetDomain 6 (by decide)) k = ReedSolomon.code domain k := by
  constructor
  · exact code_eq_of_dilation domain _ (Units.mk0 122764 (by decide)) (fun _ => rfl) k
  · exact code_eq_of_dilation domain _ (Units.mk0 6 (by decide)) (fun _ => rfl) k

#print axioms code_eq_of_dilation
#print axioms coset_codes
#print axioms complete_edges
#print axioms balanced_row
#print axioms cosets_disjoint
#print axioms coset_discrepancies

end ProximityGap.PaleyCodingCosets
