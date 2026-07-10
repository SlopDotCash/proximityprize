/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86DepthFiveConstantGap
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic

/-!
# G87: repeated-coordinate depth-five strata lose a full power of n

G86 localizes the generic depth-five route to a constant-factor gap after ordering symmetries.
Repeated-coordinate cores must be separated because the coordinate-permutation action has
stabilizers.  Fortunately they occupy a smaller ambient universe.

The exact number of noninjective words `Fin 5 → Fin n` is `n^5 - (n)_5`.  For an equal-sum pair
with a noninjective word on one side, four coordinates on the other side determine the fifth.
Allowing either side to be noninjective gives the explicit cover type below.  At production order
its cardinality is at most `20*n^8`; after the already-landed free subgroup scaling this yields at
most `20*n^7` orbit classes, and that entire corrected-padding contribution fits the Wick budget.

The theorem is an arithmetic/counting consumer.  The concrete equal-sum core family must still
inject into this cover and carry the free scaling action, as in G83.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87DepthFiveRepeatedStrata

open G86DepthFiveConstantGap

/-- Noninjective ordered words of length five. -/
abbrev NonInjectiveFive (n : ℕ) :=
  {f : Fin 5 → Fin n // ¬ Function.Injective f}

/-- Injective words are exactly embeddings. -/
def injectiveFiveEquivEmbedding (n : ℕ) :
    {f : Fin 5 → Fin n // Function.Injective f} ≃ (Fin 5 ↪ Fin n) where
  toFun f := ⟨f.1, f.2⟩
  invFun e := ⟨e, e.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact noninjective-word census. -/
theorem card_nonInjectiveFive (n : ℕ) :
    Fintype.card (NonInjectiveFive n) = n ^ 5 - n.descFactorial 5 := by
  classical
  rw [Fintype.card_subtype_compl (fun f : Fin 5 → Fin n => Function.Injective f)]
  rw [Fintype.card_congr (injectiveFiveEquivEmbedding n)]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_embedding_eq]

/-- A deliberately redundant cover for equal-sum pairs with a repeated coordinate on at least one
side: record the noninjective side and four free coordinates of the other side, plus orientation. -/
abbrev RepeatedEqualSumCover (n : ℕ) :=
  (NonInjectiveFive n × (Fin 4 → Fin n)) ⊕
    ((Fin 4 → Fin n) × NonInjectiveFive n)

theorem card_repeatedEqualSumCover (n : ℕ) :
    Fintype.card (RepeatedEqualSumCover n) =
      2 * (n ^ 5 - n.descFactorial 5) * n ^ 4 := by
  simp only [RepeatedEqualSumCover, Fintype.card_sum, Fintype.card_prod,
    card_nonInjectiveFive, Fintype.card_fun, Fintype.card_fin]
  ring

/-- Production cover bound. -/
theorem production_card_repeatedEqualSumCover_le :
    Fintype.card (RepeatedEqualSumCover (2 ^ 30)) ≤ 20 * (2 ^ 30) ^ 8 := by
  rw [card_repeatedEqualSumCover]
  norm_num [Nat.descFactorial]

/-- Dividing the repeated cover by a free size-n scaling action leaves at most `20*n^7` classes. -/
theorem production_repeated_orbit_count_le
    {J : ℕ}
    (hfreeCover : (2 ^ 30) * J ≤ Fintype.card (RepeatedEqualSumCover (2 ^ 30))) :
    J ≤ 20 * (2 ^ 30) ^ 7 := by
  have hmul : (2 ^ 30) * J ≤ (2 ^ 30) * (20 * (2 ^ 30) ^ 7) := by
    calc
      (2 ^ 30) * J ≤ Fintype.card (RepeatedEqualSumCover (2 ^ 30)) := hfreeCover
      _ ≤ 20 * (2 ^ 30) ^ 8 := production_card_repeatedEqualSumCover_le
      _ = (2 ^ 30) * (20 * (2 ^ 30) ^ 7) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)

/-- The entire repeated-coordinate depth-five orbit budget fits the production Wick bound. -/
theorem production_depth_five_repeated_orbits_absorbed :
    20 * (2 ^ 30) ^ 7 * correctedEnvelope (2 ^ 30) 110 1 5 ≤
      Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  norm_num [correctedEnvelope, Nat.descFactorial, Nat.factorial, Nat.doubleFactorial]

/-- Consumer combining the free-cover count with the corrected padded-sector envelope. -/
theorem production_depth_five_repeated_sector_absorbed
    {J W : ℕ}
    (hfreeCover : (2 ^ 30) * J ≤ Fintype.card (RepeatedEqualSumCover (2 ^ 30)))
    (hW : W ≤ J * correctedEnvelope (2 ^ 30) 110 1 5) :
    W ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 := by
  calc
    W ≤ J * correctedEnvelope (2 ^ 30) 110 1 5 := hW
    _ ≤ (20 * (2 ^ 30) ^ 7) * correctedEnvelope (2 ^ 30) 110 1 5 := by
      gcongr
      exact production_repeated_orbit_count_le hfreeCover
    _ ≤ Nat.doubleFactorial (2 * 110 - 1) * (2 ^ 30) ^ 110 :=
      production_depth_five_repeated_orbits_absorbed

end ArkLib.ProximityGap.Frontier.G87DepthFiveRepeatedStrata

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G87DepthFiveRepeatedStrata.card_nonInjectiveFive
#print axioms
  ArkLib.ProximityGap.Frontier.G87DepthFiveRepeatedStrata.production_depth_five_repeated_sector_absorbed
