/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Markov anti-concentration of the subgroup Gauss sum (#357)

`SubgroupGaussSumSecondMoment` proves, elementarily (Parseval, no Weil),
`∑_{b∈F} ‖η_b‖² = q·|G|` for the subgroup Gauss sum `η_b = ∑_{y∈G} ψ(b·y)`. The average is therefore
`|G|`, so the *typical* `‖η_b‖` is `√|G| ≪ √q` (dossier §24): the proximity count beats the Johnson
`√q` scale on average over frequencies.

This file makes that quantitative via Markov's inequality, with NO Weil input: only a few frequencies
can reach the full-field (Johnson) scale.

* `card_large_frequencies_mul_le` — Markov: for any threshold `τ > 0`,
  `#{b : ‖η_b‖² ≥ τ} · τ ≤ q·|G|`.
* `card_johnson_scale_frequencies_le` — the headline at the Johnson scale `τ = q`:
  **`#{b : ‖η_b‖² ≥ q} ≤ |G|`.** At most `|G|` of the `q` frequencies attain the full-field `√q`
  magnitude; the remaining `≥ q − |G|` are strictly below it. This is the exact, machine-checked
  quantitative form of "the average over frequencies beats Johnson" — the proven half of the
  average/worst-case duality (dossier §24–26). It does NOT pin `δ*`: the worst-case list bound is
  governed by the WORST frequency for an *adversarial* `(p, w)`, which a count bound does not control
  (that is the open core, regime III). It is the honest average-side quantitative anchor.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Markov inequality for the subgroup Gauss sum.** From the exact second moment
`∑_b ‖η_b‖² = q·|G|`, for any threshold `τ > 0` the number of frequencies whose squared Gauss sum
reaches `τ` satisfies `#{b : ‖η_b‖² ≥ τ}·τ ≤ q·|G|`. (No Weil input — pure Parseval + Markov.) -/
theorem card_large_frequencies_mul_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {τ : ℝ} :
    ((Finset.univ.filter (fun b : F => τ ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) * τ
      ≤ (Fintype.card F : ℝ) * G.card := by
  classical
  set S := Finset.univ.filter (fun b : F => τ ≤ ‖eta ψ G b‖ ^ 2) with hS
  calc ((S.card : ℝ)) * τ
      = ∑ _b ∈ S, τ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun b _ _ => by positivity)
    _ = (Fintype.card F : ℝ) * G.card := subgroup_gaussSum_secondMoment hψ G

/-- **At most `|G|` frequencies reach the Johnson (full-field) scale.** Specializing Markov to the
threshold `τ = q = |F|`: `#{b : ‖η_b‖² ≥ q} ≤ |G|`. Since `|G| ≤ q`, at least `q − |G|` of the
frequencies have `‖η_b‖ < √q`, i.e. strictly beat the Johnson scale. The exact, Weil-free quantitative
form of the average-side cancellation (dossier §24); the worst-case per-frequency bound for an
adversarial instance — the open core — is untouched. -/
theorem card_johnson_scale_frequencies_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 0 < Fintype.card F) :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card ≤ G.card := by
  classical
  have hmul := card_large_frequencies_mul_le hψ G (τ := (Fintype.card F : ℝ))
  set S := Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)
  have hqR : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  -- `|S|·q ≤ q·|G|` ⟹ `|S| ≤ |G|` over ℝ, then cast to ℕ
  have hle : (S.card : ℝ) ≤ (G.card : ℝ) := by
    have h := hmul
    rw [mul_comm (Fintype.card F : ℝ) (G.card : ℝ)] at h
    exact le_of_mul_le_mul_right h hqR
  exact_mod_cast hle

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.card_large_frequencies_mul_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.card_johnson_scale_frequencies_le
