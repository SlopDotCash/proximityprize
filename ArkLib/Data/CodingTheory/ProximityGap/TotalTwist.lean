/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaCosetSplit

/-!
# The total-twist Parseval identity (#407)

Summing the deficit-twist identity (`eta_split_parallelogram`) over **all** frequencies and applying
Parseval (`subgroup_gaussSum_secondMoment`, plus the reindexing `b ↦ ωb`) gives the exact

> **`total_twist_eq`** — `∑_b ‖η_H(b) − η_H(ωb)‖² = q·|G|`.

So the **average** twist over frequencies is exactly `|G| = n` — the same as the average squared
period. This is a sharp obstruction to *averaging* the C1 tower lead: the worst-frequency twist that
a tower deficit needs is `Θ(n)` *at the single worst frequency* (where `‖η_G‖² ~ n log q`), but the
twist budget spread over all `q` frequencies averages only `n`. The deficit cannot be extracted from
the mean — it is irreducibly a worst-case (BGK) statement, confirming the structural cap.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.EtaCosetSplit

namespace ArkLib.ProximityGap.TotalTwist

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Total-twist Parseval identity.** The sum of the deficit-twist over all frequencies equals
`q·|G|`; equivalently the average twist is exactly `|G|`. Worst-case `Θ(n)` twist at the worst
frequency cannot be read off this mean — the C1 deficit is irreducibly worst-case (BGK). -/
theorem total_twist_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G H : Finset F} {ω : F} (hω : ω ≠ 0)
    (hG : G = H ∪ H.image (fun x => ω * x))
    (hdisj : Disjoint H (H.image (fun x => ω * x))) :
    ∑ b : F, ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2 = (Fintype.card F : ℝ) * G.card := by
  -- card relation |G| = 2|H|
  have hinj : Function.Injective (fun x : F => ω * x) := mul_right_injective₀ hω
  have hcard : (G.card : ℝ) = 2 * H.card := by
    rw [hG, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj]
    push_cast; ring
  -- summed parallelogram
  have hsum : ∑ b : F, (‖eta ψ G b‖ ^ 2 + ‖eta ψ H b - eta ψ H (ω * b)‖ ^ 2)
      = ∑ b : F, 2 * (‖eta ψ H b‖ ^ 2 + ‖eta ψ H (ω * b)‖ ^ 2) :=
    Finset.sum_congr rfl (fun b _ => eta_split_parallelogram (ψ := ψ) hω hG hdisj b)
  rw [Finset.sum_add_distrib] at hsum
  -- Parseval pieces
  have hG2 := subgroup_gaussSum_secondMoment hψ G
  have hH2 := subgroup_gaussSum_secondMoment hψ H
  have hreindex : ∑ b : F, ‖eta ψ H (ω * b)‖ ^ 2 = ∑ b : F, ‖eta ψ H b‖ ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft₀ ω hω) _ _ (fun b => rfl)
  -- RHS = 2*(Σ‖η_H‖² + Σ‖η_H(ωb)‖²)
  have hRHS : ∑ b : F, 2 * (‖eta ψ H b‖ ^ 2 + ‖eta ψ H (ω * b)‖ ^ 2)
      = 2 * ((Fintype.card F : ℝ) * H.card + (Fintype.card F : ℝ) * H.card) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hreindex, hH2]
  rw [hG2, hRHS] at hsum
  rw [hcard] at hsum ⊢
  linear_combination hsum

end ArkLib.ProximityGap.TotalTwist
#print axioms ArkLib.ProximityGap.TotalTwist.total_twist_eq
