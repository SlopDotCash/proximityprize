/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier._RSLocatorExtension
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-! # Comparing MCA probabilities after Reed–Solomon shortening

Locator extension carries every bad scalar of a received pair into a single
longer received pair with the same integer error count.
-/
set_option autoImplicit false
noncomputable section
open Finset Code
open _root_.ProximityGap
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.LocatorShortening
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n N k : ℕ}

omit [Field F] [DecidableEq F] in
/-- Embed the old coordinates into a domain of any intermediate length in the same field. -/
theorem exists_extended_domain (dom : Fin n ↪ F) (hlen : n ≤ N)
    (hfield : N ≤ Fintype.card F) :
    ∃ (old : Fin n ↪ Fin N) (dom' : Fin N ↪ F), old.trans dom' = dom := by
  classical
  let A : Finset F := Finset.univ.map dom
  have hA : A.card = n := by simp [A]
  obtain ⟨T, hAT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ A) (hA.trans_le hlen) (by simpa using hfield)
  let e := T.equivFinOfCardEq hT
  let intoT : Fin n ↪ ↥T :=
    ⟨fun i => ⟨dom i, hAT (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩,
      fun _ _ h => dom.injective (congrArg Subtype.val h)⟩
  refine ⟨intoT.trans e.toEmbedding, e.symm.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩
  ext i
  change (e.symm (e (intoT i))).val = dom i
  rw [e.symm_apply_apply]
  rfl

/-- A grid radius at integer error count has exactly the complementary agreement mass. -/
theorem agreement_mass (m t : ℕ) [NeZero m] :
    (1 - (t : ℝ≥0) / (m : ℝ≥0)) * (m : ℝ≥0) = ((m - t : ℕ) : ℝ≥0) := by
  have hm : (m : ℝ≥0) ≠ 0 := by exact_mod_cast NeZero.ne m
  rw [tsub_mul, one_mul, div_mul_cancel₀ _ hm, Nat.cast_tsub]

/-- Adding evaluation sites while raising the dimension by their number can only
increase the worst MCA probability at a fixed integer error count. -/
theorem eps_le_extension [NeZero n] [NeZero N] (old : Fin n ↪ Fin N) (D : Fin N ↪ F)
    (hk : 0 < k) (e : ℕ) :
    epsMCA (F := F) (ReedSolomon.code (old.trans D) k : Set (Fin n → F)) ((e : ℝ≥0) / n) ≤
      epsMCA (F := F) (ReedSolomon.code D (k + (N-n)) : Set (Fin N → F)) ((e : ℝ≥0) / N) := by
  classical
  have hlen : n ≤ N := by simpa using Fintype.card_le_of_embedding old
  have hsize (a : ℕ) (ha : (1-(e:ℝ≥0)/n)*n ≤ (a:ℝ≥0)) :
      (1-(e:ℝ≥0)/N)*N ≤ ((a+(N-n):ℕ):ℝ≥0) := by
    rw [agreement_mass] at ha ⊢
    have h : n-e ≤ a := by exact_mod_cast ha
    exact_mod_cast (show N-e ≤ a+(N-n) by omega)
  rw [epsMCA_eq_iSup_badCount_div, epsMCA_eq_iSup_badCount_div]
  apply ENNReal.div_le_div_right _ _
  apply iSup_le
  intro u
  let v : WordStack F (Fin 2) (Fin N) := fun b => RSLocatorExtension.extendWord old D (u b)
  apply le_iSup_of_le v
  exact_mod_cast RSLocatorExtension.badScalar_card_le_extension old D hk hsize (u 0) (u 1)

#print axioms eps_le_extension
end ArkLib.ProximityGap.Frontier.LocatorShortening
