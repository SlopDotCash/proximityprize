/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SharedLocatorListIncidences

/-! # One agreement anchor reduces a quadratic list to an affine incidence configuration -/
noncomputable section
open Finset Code Polynomial
namespace ProximityGap.QuadraticListIncidences
open AffineListIncidences

variable {F I : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- The interpolation cost need only hold for the affine list shortened at one
well-populated site. All finite interleaving widths obey the resulting budget. -/
theorem list_bound (dom : I ↪ F) (n t B l : ℕ) (hn : Fintype.card I = n)
    (ht : t ≤ n) (hl : 0 < l) (havg : n * (l - 1) < (B + 1) * t)
    (hfield : (B + 1).choose 2 ≤ Nat.card F)
    (estimate : ∀ P L : Finset (F × F), P.card = n - 1 → L.card = l →
      incidences P L < l * (t - 1)) (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      (((n - t : ℕ) : ℝ) / n) ≤ B := by
  apply InterleavedListProjection.interleaved_le_of_scalar_le _ _ _ hfield
  exact SharedLocatorListIncidences.scalar_bound dom n t B l 1 hn ht hl (by simpa using havg) estimate

/-- With a budget of eight times the domain length only 44,429 agreements are required. -/
theorem eight_lengths (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (8589934593 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 71085)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      ((1073697395 : ℝ) / 1073741824) ≤ (8589934592 : ℕ) :=
  list_bound dom 1073741824 44429 8589934592 355433 hn (by decide) (by decide) (by decide) hfield
    (fun P L m s => by
      have h := graph P L
      rw [m, s] at h
      exact h.trans_lt (by decide)) width

/-- With a budget of 64 times the domain length only 26,412 agreements are required. -/
theorem sixty_four_lengths (dom : I ↪ F) (hn : Fintype.card I = 1073741824)
    (hfield : (68719476737 : ℕ).choose 2 ≤ Nat.card F) (graph : GraphEstimate F 120739)
    (width : ℕ) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code dom 3 : Set (I → F)))
      ((1073715412 : ℝ) / 1073741824) ≤ (68719476736 : ℕ) :=
  list_bound dom 1073741824 26412 68719476736 1690369 hn (by decide) (by decide) (by decide) hfield
    (fun P L m s => by
      have h := graph P L
      rw [m, s] at h
      exact h.trans_lt (by decide)) width

#print axioms eight_lengths
#print axioms sixty_four_lengths
end ProximityGap.QuadraticListIncidences
