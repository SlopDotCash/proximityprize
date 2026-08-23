/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24KernelVector

/-!
# [AGL24] the agreement-forcing endgame step (issue #346, brick 22)

The final move of the Appendix A proof: *since `y` and `c⁽ʲ⁾` are evaluations of
degree-less-than-`k` polynomials agreeing on at least `k` indices, `y = c⁽ʲ⁾`*. Combined
with brick 21's vertex-degree bound, this collapses the whole configuration to zero.

* `coeff_eq_of_agree` — **the forcing**: two coefficient vectors over `Fin k` whose monomial
  evaluations agree at `≥ k` points of an injective evaluation map are equal (the difference
  polynomial has degree `< k` and `≥ k` distinct roots);
* `rsEval_eq_of_agree` — the same statement on the campaign's `rsEval` surface.
-/

open Finset Polynomial

namespace AGL24

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [DecidableEq F]

/-- **The degree-`< k` agreement forcing**: coefficient vectors whose evaluations agree at
`≥ k` points of an injective evaluation map coincide. -/
theorem coeff_eq_of_agree {k : ℕ} (α : ι → F) (hα : Function.Injective α)
    (f g : Fin k → F)
    (hagree : k ≤ (Finset.univ.filter (fun i =>
      ∑ m : Fin k, f m * (α i) ^ (m : ℕ) = ∑ m : Fin k, g m * (α i) ^ (m : ℕ))).card) :
    f = g := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · funext m
    exact absurd m.isLt (by omega)
  -- The difference polynomial.
  set p : Polynomial F := ∑ m : Fin k, Polynomial.C (f m - g m) * Polynomial.X ^ (m : ℕ)
    with hp
  -- Degree < k.
  have hdeg : p.natDegree < k := by
    have hle : p.natDegree ≤ k - 1 := by
      rw [hp]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun m _ => ?_⟩
      simp only [Function.comp]
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
      have := m.isLt
      omega
    omega
  -- Agreeing indices give roots.
  have hroot : ∀ i, (∑ m : Fin k, f m * (α i) ^ (m : ℕ)
      = ∑ m : Fin k, g m * (α i) ^ (m : ℕ)) → p.eval (α i) = 0 := by
    intro i hi
    rw [hp, Polynomial.eval_finset_sum]
    have : ∀ m : Fin k, ((Polynomial.C (f m - g m) * Polynomial.X ^ (m : ℕ)).eval (α i))
        = (f m - g m) * (α i) ^ (m : ℕ) := fun m => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Finset.sum_congr rfl fun m _ => this m]
    have hsplit : ∑ m : Fin k, (f m - g m) * (α i) ^ (m : ℕ)
        = ∑ m : Fin k, f m * (α i) ^ (m : ℕ) - ∑ m : Fin k, g m * (α i) ^ (m : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hsplit, hi, sub_self]
  -- p must vanish: otherwise too many roots.
  have hp0 : p = 0 := by
    by_contra hne
    have hsubset : (Finset.univ.filter (fun i =>
        ∑ m : Fin k, f m * (α i) ^ (m : ℕ) = ∑ m : Fin k, g m * (α i) ^ (m : ℕ))).image α
        ⊆ p.roots.toFinset := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      rw [Finset.mem_filter] at hi
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hroot i hi.2
    have hcards : k ≤ p.roots.toFinset.card := by
      calc k ≤ (Finset.univ.filter (fun i =>
          ∑ m : Fin k, f m * (α i) ^ (m : ℕ)
            = ∑ m : Fin k, g m * (α i) ^ (m : ℕ))).card := hagree
      _ = ((Finset.univ.filter (fun i =>
          ∑ m : Fin k, f m * (α i) ^ (m : ℕ)
            = ∑ m : Fin k, g m * (α i) ^ (m : ℕ))).image α).card :=
            (Finset.card_image_of_injective _ hα).symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsubset
    have : p.roots.toFinset.card ≤ p.natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)
    omega
  -- Zero polynomial: coefficients agree.
  funext m₀
  have hcoeff := congrArg (fun q => Polynomial.coeff q (m₀ : ℕ)) hp0
  rw [hp] at hcoeff
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single m₀ (fun m _ hne => by
      rw [if_neg (fun h => hne (Fin.ext (by exact_mod_cast h.symm))), mul_zero])
    (fun h => absurd (Finset.mem_univ m₀) h)] at hcoeff
  rw [if_pos rfl, mul_one] at hcoeff
  have := sub_eq_zero.mp hcoeff
  exact this

/-- The forcing on the campaign's `rsEval` surface: subfamily members agreeing at `≥ k`
points coincide. -/
theorem rsEval_eq_of_agree {t k : ℕ} (α : ι → F) (hα : Function.Injective α)
    (g : Fin (t + 1) → Fin k → F) (j j' : Fin (t + 1))
    (hagree : k ≤ (Finset.univ.filter (fun i =>
      rsEval α g j i = rsEval α g j' i)).card) :
    g j = g j' := by
  exact coeff_eq_of_agree α hα (g j) (g j') hagree

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.coeff_eq_of_agree
#print axioms AGL24.rsEval_eq_of_agree
