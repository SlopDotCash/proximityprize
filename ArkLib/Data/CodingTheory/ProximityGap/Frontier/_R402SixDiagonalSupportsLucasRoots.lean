/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R397DiagonalPairLucasReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R401PairMultiplicityTenSupportReduction

/-!
# R402: six diagonal pair supports give six distinct Lucas common roots

For six pair representations of `2`, map each support to the product of its endpoints. R397 proves
that fixed-sum distinct supports have distinct products and that each product satisfies

`s^n = 1`, `pairLucas s n = 2`.

This file packages the six-support obstruction in the exact form consumed by a degree-five
subresultant certificate: six distinct common roots of those two equations.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R402SixDiagonalSupportsLucasRoots

open ArkLib.ProximityGap.Frontier.R395PairMultiplicitySixRootReduction
open ArkLib.ProximityGap.Frontier.R397DiagonalPairLucasReduction

variable {F : Type*} [Field F] [DecidableEq F]

/-- Products attached to six ordered pair representatives. -/
noncomputable def sixProducts (u : Fin 6 → Fin 2 → F) : Finset F :=
  Finset.univ.image (fun a => u a 0 * u a 1)

/-- Distinct fixed-sum supports give six distinct products. -/
theorem card_sixProducts
    (u : Fin 6 → Fin 2 → F)
    (hsum : ∀ a, ∑ i, u a i = 2)
    (hsupport : Function.Injective (fun a => pairSupport (u a))) :
    (sixProducts u).card = 6 := by
  classical
  rw [sixProducts, Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    by_contra hne
    have hsne : pairSupport (u a) ≠ pairSupport (u b) := by
      intro hs
      exact hne (hsupport hs)
    have hsumab : u a 0 + u a 1 = u b 0 + u b 1 := by
      simpa [Fin.sum_univ_two] using (hsum a).trans (hsum b).symm
    exact (product_ne_of_pairSupport_ne
      (x := u a 0) (y := u a 1) (x' := u b 0) (y' := u b 1) hsumab hsne) hab

/-- Every product in the six-element image is a common root of the Lucas equations. -/
theorem mem_sixProducts_common_root
    {u : Fin 6 → Fin 2 → F} {n : ℕ}
    (hsum : ∀ a, ∑ i, u a i = 2)
    (hroot : ∀ a i, (u a i) ^ n = 1)
    {s : F} (hs : s ∈ sixProducts u) :
    s ^ n = 1 ∧ pairLucas s n = 2 := by
  classical
  rw [sixProducts, Finset.mem_image] at hs
  obtain ⟨a, _, rfl⟩ := hs
  exact lucas_common_root_of_pair (by simpa [Fin.sum_univ_two] using hsum a)
    (hroot a 0) (hroot a 1)

/-- **Six-support Lucas obstruction.** The common-root locus contains at least six elements. -/
theorem six_le_card_commonRootFilter
    (u : Fin 6 → Fin 2 → F) (n : ℕ)
    (hsum : ∀ a, ∑ i, u a i = 2)
    (hroot : ∀ a i, (u a i) ^ n = 1)
    (hsupport : Function.Injective (fun a => pairSupport (u a))) :
    6 ≤ ((sixProducts u).filter (fun s => s ^ n = 1 ∧ pairLucas s n = 2)).card := by
  have hall : (sixProducts u).filter (fun s => s ^ n = 1 ∧ pairLucas s n = 2) =
      sixProducts u := by
    apply Finset.filter_eq_self.mpr
    intro s hs
    exact mem_sixProducts_common_root hsum hroot hs
  rw [hall, card_sixProducts u hsum hsupport]

end ArkLib.ProximityGap.Frontier.R402SixDiagonalSupportsLucasRoots

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R402SixDiagonalSupportsLucasRoots.six_le_card_commonRootFilter
