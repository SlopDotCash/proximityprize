/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import MathCollab.IncidenceSharper
import ArkLib.Research.ProximityGap.Frontier.QuadraticListIncidences
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-! # Named affine-list bounds with the external incidence proof linked -/
open Code
namespace ProximityGap.AffineNamedEndpoints
open AffineListIncidences
variable {I : Type} [Fintype I] [Nonempty I]

/-- Lewko's discrete graph theorem on the project's pinned Lean and mathlib. -/
theorem graph {F : Type} [Field F] [DecidableEq F] {d : ℕ} (hd : d < ringChar F) :
    GraphEstimate F d := by
  classical
  intro P L
  have same : incidences P L = MathCollab.IncidenceCounting.count P L
      MathCollab.IncidenceCounting.onGraph := by
    unfold incidences MathCollab.IncidenceCounting.count
    apply Finset.sum_congr rfl
    intro l _
    apply congrArg Finset.card
    exact @Finset.filter_congr_decidable _ P
      (fun q => q.2 = l.1 * q.1 + l.2)
      (fun q => inferInstanceAs (Decidable (q.2 = l.1 * q.1 + l.2)))
      (fun q => Classical.propDecidable (MathCollab.IncidenceCounting.onGraph q l))
  rw [same]
  exact MathCollab.IncidenceSharper.graph_discrete P L d (Or.inr hd)

namespace First
open ArkLib.ProximityGap.PrizeShapePrimeP30
local instance : Fact P.Prime := ⟨prime_P⟩

/-- At the first 128-bit budget every closed list of affine words has size at most
2³⁰ when each word agrees at 3073 sites of an arbitrary length-2³⁰ domain. -/
theorem affine_list_budget (dom : I ↪ ZMod P) (hn : Fintype.card I = 1073741824) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 2 : Set (I → ZMod P)))
      ((1073738751 : ℝ) / 1073741824) ≤ (P / 2 ^ 128 : ℕ) := by
  apply AffineListIncidences.first dom hn
  · norm_num [Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right, P]
  · exact graph (by rw [ringChar.eq (ZMod P) P]; decide)
end First

namespace Second
open ArkLib.ProximityGap.PrizeShapePrimeP30Second
local instance : Fact P.Prime := ⟨prime_P⟩

/-- The second named bound uses slope-intercept duality and 2439 agreements. -/
theorem affine_list_budget (dom : I ↪ ZMod P) (hn : Fintype.card I = 1073741824) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 2 : Set (I → ZMod P)))
      ((1073739385 : ℝ) / 1073741824) ≤ (P / 2 ^ 128 : ℕ) := by
  apply AffineListIncidences.second dom hn
  · norm_num [Nat.card_eq_fintype_card, ZMod.card, Nat.choose_two_right, P]
  · exact graph (by rw [ringChar.eq (ZMod P) P]; decide)
end Second

/-- Every prime at or above the eight-length 128-bit budget meets its actual list
budget at 44,429 agreements for dimension three, on any evaluation domain. -/
theorem quadratic_eight {p : ℕ} [Fact p.Prime] (hb : 8589934592 ≤ p / 2 ^ 128)
    (dom : I ↪ ZMod p) (hn : Fintype.card I = 1073741824) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → ZMod p)))
      ((1073697395 : ℝ) / 1073741824) ≤ (p / 2 ^ 128 : ℕ) := by
  have actual : (2 ^ 128 : ℕ) ≤ p := by omega
  apply le_trans (QuadraticListIncidences.eight_lengths dom hn ?_ ?_ width)
  · exact_mod_cast hb
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    exact (show (8589934593 : ℕ).choose 2 ≤ 2 ^ 128 by norm_num [Nat.choose_two_right]).trans actual
  · exact graph (by rw [ringChar.eq (ZMod p) p]; omega)

/-- The analogous sixty-four-length prime-field bound needs 26,412 agreements. -/
theorem quadratic_sixty_four {p : ℕ} [Fact p.Prime] (hb : 68719476736 ≤ p / 2 ^ 128)
    (dom : I ↪ ZMod p) (hn : Fintype.card I = 1073741824) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → ZMod p)))
      ((1073715412 : ℝ) / 1073741824) ≤ (p / 2 ^ 128 : ℕ) := by
  have actual : (2 ^ 128 : ℕ) ≤ p := by omega
  apply le_trans (QuadraticListIncidences.sixty_four_lengths dom hn ?_ ?_ width)
  · exact_mod_cast hb
  · rw [Nat.card_eq_fintype_card, ZMod.card]
    exact (show (68719476737 : ℕ).choose 2 ≤ 2 ^ 128 by norm_num [Nat.choose_two_right]).trans actual
  · exact graph (by rw [ringChar.eq (ZMod p) p]; omega)

/-- In every dimension s+2, a sufficiently large actual 128-bit budget meets the
closed-list requirement at s+3073 agreements on any prime-field domain of length 2³⁰. -/
theorem near_capacity {p : ℕ} [Fact p.Prime] (dom : I ↪ ZMod p)
    (hn : Fintype.card I = 1073741824) (s : ℕ) (ht : s + 3073 ≤ 1073741824)
    (hb : 1073741824 * (1073741824 : ℕ).choose s ≤ (p / 2 ^ 128) * (s + 3073).choose s)
    (width : ℕ) [NeZero width] :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom (s + 2) : Set (I → ZMod p)))
      (((1073741824 - (s + 3073) : ℕ) : ℝ) / 1073741824) ≤ (p / 2 ^ 128 : ℕ) := by
  have dp := Fintype.card_le_of_injective _ dom.injective
  rw [hn, ZMod.card] at dp
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using
    SharedLocatorListIncidences.production dom s hn ht
      (graph (by rw [ringChar.eq (ZMod p) p]; omega))
      (by simpa only [Nat.card_eq_fintype_card, ZMod.card] using hb) width

#print axioms near_capacity
#print axioms quadratic_eight
#print axioms quadratic_sixty_four
#print axioms First.affine_list_budget
#print axioms Second.affine_list_budget
end ProximityGap.AffineNamedEndpoints
