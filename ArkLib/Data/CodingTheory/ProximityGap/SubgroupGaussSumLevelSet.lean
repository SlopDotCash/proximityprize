/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# Frequency concentration for the subgroup Gauss sum (#389)

A Markov / level-set bound from the second moment `∑_b ‖η_b‖² = q|G|`
(`SubgroupGaussSumSecondMoment`): the number of "bad" frequencies — those whose incomplete
character sum `η_b = ∑_{y∈G} ψ(b·y)` is large — is small.

> **`card_high_frequency_le`** — `#{b : ‖η_b‖² ≥ T} · T ≤ q·|G|`, i.e. at most `q|G|/T`
> frequencies have `‖η_b‖² ≥ T`.

Taking `T = λ·|G|`: all but a `q/λ` fraction of frequencies obey `‖η_b‖ < √(λ|G|)` — the
square-root cancellation `|η_b| = O(√|G|)` holds for *almost all* frequencies (the average case).
The δ\* interior residual is precisely the *worst case over all `b≠0`* (the open Bourgain regime,
CLAUDE.md face #3); this lemma pins that the failure, if any, is confined to a sparse set of
frequencies. Axiom-clean. Issue #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.SubgroupGaussSumLevelSet

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Markov level-set bound.** At most `q|G|/T` frequencies have `‖η_b‖² ≥ T`. -/
theorem card_high_frequency_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (T : ℝ) :
    ((Finset.univ.filter (fun b => T ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) * T
      ≤ (Fintype.card F : ℝ) * G.card := by
  set S := Finset.univ.filter (fun b => T ≤ ‖eta ψ G b‖ ^ 2) with hS
  have h1 : (S.card : ℝ) * T = ∑ _b ∈ S, T := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _b ∈ S, T ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
  have h3 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 ≤ ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => sq_nonneg _)
  rw [h1]
  calc ∑ _b ∈ S, T
      ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 := h2
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 2 := h3
    _ = (Fintype.card F : ℝ) * G.card := subgroup_gaussSum_secondMoment hψ G

/-- **Almost-all frequencies have `√|G|` cancellation.** For `λ > 0` and `0 < |G|`, the number of
frequencies with `‖η_b‖² ≥ λ·|G|` is at most `q/λ`. -/
theorem card_high_frequency_le_div {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {lam : ℝ} (hlam : 0 < lam) (hG : 0 < G.card) :
    ((Finset.univ.filter (fun b => lam * G.card ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      ≤ (Fintype.card F : ℝ) / lam := by
  have hkey := card_high_frequency_le hψ G (lam * G.card)
  have hGpos : (0 : ℝ) < G.card := by exact_mod_cast hG
  rw [le_div_iff₀ hlam]
  -- `card · (λ·|G|) ≤ q·|G|` ⟹ `card · λ ≤ q` (cancel the positive `|G|`)
  have hcancel : ((Finset.univ.filter (fun b => lam * G.card ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
      * lam * G.card ≤ (Fintype.card F : ℝ) * G.card := by
    calc ((Finset.univ.filter (fun b => lam * G.card ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) * lam * G.card
        = ((Finset.univ.filter (fun b => lam * G.card ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
            * (lam * G.card) := by ring
      _ ≤ (Fintype.card F : ℝ) * G.card := hkey
  exact le_of_mul_le_mul_right hcancel hGpos

end ArkLib.ProximityGap.SubgroupGaussSumLevelSet

#print axioms ArkLib.ProximityGap.SubgroupGaussSumLevelSet.card_high_frequency_le
#print axioms ArkLib.ProximityGap.SubgroupGaussSumLevelSet.card_high_frequency_le_div
