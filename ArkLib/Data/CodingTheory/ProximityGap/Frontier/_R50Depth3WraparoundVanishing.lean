/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment

/-!
# Round 50: the depth-3 wraparound-vanishing atom

The round-50 probe isolated the first A-side open rung in the most concrete form currently
available: for the prize 2-power subgroup, the finite-field depth-3 additive energy appears to
equal the characteristic-zero value

`15 n^3 - 45 n^2 + 40 n`.

This file does **not** prove that arithmetic vanishing statement.  It records the exact named
input and proves the immediate machine-checked consequence: by the in-tree sixth-moment identity,
that one atom is exactly equivalent to the sixth moment taking the characteristic-zero value.
This gives future attempts a small, typed target instead of a prose note in the dossier.
-/

set_option autoImplicit false
set_option linter.style.longLine false

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

namespace ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Depth-3 wraparound vanishing**, stated at the finite-field energy level.

`V3` is intended to be the characteristic-zero six-term relation count for the same 2-power
subgroup, for example `15 n^3 - 45 n^2 + 40 n` when the Lam-Leung depth-3 closed form applies.
The open arithmetic content is precisely `addEnergy3 G = V3`: no mod-`p` sextuple collision exists
unless it already comes from a characteristic-zero collision. -/
def Depth3WraparoundVanishing (G : Finset F) (V3 : ℕ) : Prop :=
  addEnergy3 G = V3

/-- The sixth moment immediately takes the supplied characteristic-zero value once the depth-3
wraparound-vanishing atom is available. -/
theorem sixthMoment_eq_of_depth3WraparoundVanishing {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {V3 : ℕ} (hvan : Depth3WraparoundVanishing G V3) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6 = (Fintype.card F : ℝ) * (V3 : ℝ) := by
  rw [subgroup_gaussSum_sixthMoment hψ G, hvan]

/-- Real-valued closed-form interface for the round-50 atom.

This is the exact statement the probe suggests for 2-power subgroups in the `p ≥ n^3` range:
if the finite-field depth-3 energy has the characteristic-zero closed form
`15n^3 - 45n^2 + 40n`, then the sixth moment is `q` times that same value. -/
theorem sixthMoment_eq_charZero_closedForm_of_depth3WraparoundVanishing {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F)
    (hvan :
      (addEnergy3 G : ℝ)
        = 15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6
      = (Fintype.card F : ℝ)
        * (15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) := by
  rw [subgroup_gaussSum_sixthMoment hψ G, hvan]

/-- Bound form of the same bridge.  Once the round-50 atom is proved and its characteristic-zero
value is bounded by `B`, the sixth moment is bounded by `q * B`. -/
theorem sixthMoment_le_of_depth3WraparoundVanishing_bound {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) {B : ℝ}
    (hvan :
      (addEnergy3 G : ℝ)
        = 15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ))
    (hB : 15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ) ≤ B) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6 ≤ (Fintype.card F : ℝ) * B := by
  rw [sixthMoment_eq_charZero_closedForm_of_depth3WraparoundVanishing hψ G hvan]
  exact mul_le_mul_of_nonneg_left hB (by exact_mod_cast Nat.zero_le (Fintype.card F))

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The characteristic-zero depth-3 closed form is bounded by the Wick constant `15·|G|³` for
nonempty `G`. -/
theorem charZero_depth3_closedForm_le_fifteen_card_cube
    (G : Finset F) (hn : 1 ≤ G.card) :
    15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)
      ≤ 15 * (G.card : ℝ) ^ 3 := by
  have hnreal : (1 : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast hn
  nlinarith [sq_nonneg ((G.card : ℝ) - 1)]

/-- Wick-constant bound form of the round-50 atom.  Once depth-3 wraparound vanishing is proved
with the characteristic-zero closed form, the sixth moment obeys the clean estimate
`∑_b ‖η_b‖⁶ ≤ 15 q |G|³`. -/
theorem sixthMoment_le_fifteen_card_cube_of_depth3WraparoundVanishing {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (hn : 1 ≤ G.card)
    (hvan :
      (addEnergy3 G : ℝ)
        = 15 * (G.card : ℝ) ^ 3 - 45 * (G.card : ℝ) ^ 2 + 40 * (G.card : ℝ)) :
    ∑ b : F, ‖eta ψ G b‖ ^ 6
      ≤ (Fintype.card F : ℝ) * (15 * (G.card : ℝ) ^ 3) :=
  sixthMoment_le_of_depth3WraparoundVanishing_bound hψ G hvan
    (charZero_depth3_closedForm_le_fifteen_card_cube G hn)

end ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.Depth3WraparoundVanishing
#print axioms ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.sixthMoment_eq_of_depth3WraparoundVanishing
#print axioms
  ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.sixthMoment_eq_charZero_closedForm_of_depth3WraparoundVanishing
#print axioms
  ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.sixthMoment_le_of_depth3WraparoundVanishing_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.charZero_depth3_closedForm_le_fifteen_card_cube
#print axioms
  ArkLib.ProximityGap.Frontier.R50Depth3WraparoundVanishing.sixthMoment_le_fifteen_card_cube_of_depth3WraparoundVanishing
