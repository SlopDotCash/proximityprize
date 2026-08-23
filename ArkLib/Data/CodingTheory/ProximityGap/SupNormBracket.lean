/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SecondMomentLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.DCOptimized

/-!
# The prize sup-norm bracket (#407)

Combining the unconditional lower bound (`SecondMomentLowerBound.exists_nonzero_frequency_ge`, some
non-trivial frequency attains the average `≈ |G|`) with the corrected conditional upper bound
(`DCOptimized.eta_sq_le_dcOptimized`, every non-trivial frequency is `≤ 2e·|G|·r`) BRACKETS the prize
sup-norm:

> **`supNorm_bracket`** — under `DCEnergyBound G r` at `r ≥ max(1, ln q)`, there is `b ≠ 0` with
> `(q|G| − |G|²)/(q−1) ≤ ‖η_b‖² ≤ 2e·|G|·r`.

So `√(|G|·(1−o(1))) ≤ M ≤ √(2e·|G|·ln q)` at `r = ⌈ln q⌉`: the sup-norm sits in `[√n, √(2e·n·ln q)]`.
The lower bound is unconditional (Parseval); the upper bound's only open input is `A_r ≤ Wick` (BGK).

Issue #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.DCEnergyCorrection ArkLib.ProximityGap.DCOptimized
open ArkLib.ProximityGap.SecondMomentLowerBound

namespace ArkLib.ProximityGap.SupNormBracket

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Prize sup-norm bracket.** Under the corrected DC energy bound at `r ≥ max(1, ln q)`, some
non-trivial frequency has its period energy between the Parseval average `(q|G|−|G|²)/(q−1) ≈ |G|` and
the optimized upper bound `2e·|G|·r`. Hence `√n ≤ M ≤ √(2e·n·ln q)`. -/
theorem supNorm_bracket {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (hr : 1 ≤ r) (hrq : Real.log (Fintype.card F) ≤ r) (hqc : 1 < Fintype.card F)
    (h : DCEnergyBound G r) :
    ∃ b : F, b ≠ 0 ∧
      ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 ∧
      ‖eta ψ G b‖ ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) := by
  obtain ⟨b, hbmem, hlow⟩ := exists_nonzero_frequency_ge hψ G hqc
  have hb : b ≠ 0 := (Finset.mem_erase.mp hbmem).1
  exact ⟨b, hb, hlow, eta_sq_le_dcOptimized hψ hr hrq h hb⟩

end ArkLib.ProximityGap.SupNormBracket
#print axioms ArkLib.ProximityGap.SupNormBracket.supNorm_bracket
