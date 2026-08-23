/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant
import ArkLib.Data.CodingTheory.ProximityGap.CompletionSharpMargin

/-!
# An UNCONDITIONAL `√q` ceiling on the canonical prize constant `Λ²` (#444)

`PrizeStructuralConstant` reduces the whole prize to the single object

  `Λ²(ψ,G) = prizeRadiusSq ψ G = max_{b≠0} ‖η_b‖²`,

with a PROVEN Parseval **floor** `Λ² ≥ (q·n − n²)/(q−1) ≈ n` and the OPEN
`DepthLogSubGaussian` **ceiling** `Λ² ≤ 2n·log q`.  The ceiling half carried no
unconditional companion: nothing in tree bounded `Λ²` from above without the open
near-Ramanujan hypothesis.

This file supplies the missing **unconditional ceiling** for the `d`-torsion subgroup, by
lifting the per-frequency completion bound `CompletionSharpMargin.norm_eta_torsion_sharp_le`
(itself EXTEND-proven off the classical Gauss-sum completion, no Weil) through the
`worstCaseIncompleteSumBound_iff_prizeRadiusSq_le` equivalence:

* **`prizeRadiusSq_torsion_le`** — `Λ²(ψ, torsion F d) ≤ (√q − (√q−1)/t)²`, `t = (q−1)/d`;
  the SHARP completion ceiling, strictly below `q`.
* **`prizeRadiusSq_torsion_lt_card`** — `Λ²(ψ, torsion F d) < q`: the prize constant is
  STRICTLY below the trivial `√q` scale (the worst frequency never attains `√q`).

Together with `prizeRadiusSq_parseval_floor` these PIN the canonical constant
unconditionally to the band `[≈ n, < q)` on the torsion subgroup, with **both** ends now
proven — and they make explicit that `DepthLogSubGaussian`'s open content is exactly the
*reduction* of this unconditional `√q` ceiling down to the `√(n·log q)` floor scale.

NOTE (honest scope, rule 3 + rule 6).  This is the classical `√q` ceiling lifted to the
sup' object; it does NOT prove CORE and is NOT thinness-essential by itself (the `√q`
ceiling holds for any torsion subgroup; the completion-margin's thin-regime *collapse* —
why this ceiling cannot be improved to the prize scale by completion — is the proven
mechanism in `CompletionSharpMargin.completion_margin_le_of_thin`).  No `δ*`/capacity/
beyond-Johnson claim; cliff-at-`n/2` not referenced.  The open `√(n·log q)` content is
untouched.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.PrizeStructuralConstant

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumWorstCase

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The unconditional sharp completion ceiling on `Λ²`.**  Lifting the per-frequency
completion bound `‖η_b‖ ≤ √q − (√q−1)/t` (every `b ≠ 0`) through the prize-constant
equivalence gives the sup' bound

  `Λ²(ψ, torsion F d) ≤ (√q − (√q−1)/t)²`,  `t = (q−1)/d`,

the first unconditional ceiling on the canonical prize object (no Weil, no open
hypothesis), strictly below the trivial `q`. -/
theorem prizeRadiusSq_torsion_le {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    prizeRadiusSq ψ (torsion F d)
      ≤ (Real.sqrt (Fintype.card F)
          - (Real.sqrt (Fintype.card F) - 1) / (((Fintype.card F - 1) / d : ℕ) : ℝ)) ^ 2 := by
  -- the per-frequency squared bound, fed through the `WorstCaseIncompleteSumBound` iff
  rw [← worstCaseIncompleteSumBound_iff_prizeRadiusSq_le]
  intro b hb
  set R : ℝ := Real.sqrt (Fintype.card F)
      - (Real.sqrt (Fintype.card F) - 1) / (((Fintype.card F - 1) / d : ℕ) : ℝ) with hR
  have hsharp : ‖eta ψ (torsion F d) b‖ ≤ R := norm_eta_torsion_sharp_le hd hd0 hψ hb
  have hnn : (0 : ℝ) ≤ ‖eta ψ (torsion F d) b‖ := norm_nonneg _
  -- `0 ≤ x ≤ R ⟹ x² ≤ R²`
  exact pow_le_pow_left₀ hnn hsharp 2

/-- **The prize constant is STRICTLY below the trivial `√q` scale.**  Since each
`‖η_b‖ < √q` (the completion margin is genuinely positive), the sup' over the (finite)
nonzero frequencies is strictly below `q`:

  `Λ²(ψ, torsion F d) < q`. -/
theorem prizeRadiusSq_torsion_lt_card {d : ℕ} (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    prizeRadiusSq ψ (torsion F d) < (Fintype.card F : ℝ) := by
  -- `Λ² = sup'_{b≠0} ‖η_b‖²`; bound each term by `‖η_b‖² < q` via the strict per-frequency bound.
  unfold prizeRadiusSq
  rw [Finset.sup'_lt_iff]
  intro b hb
  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
  have hlt : ‖eta ψ (torsion F d) b‖ < Real.sqrt (Fintype.card F) :=
    norm_eta_torsion_lt hd hd0 hψ hb0
  have hnn : (0 : ℝ) ≤ ‖eta ψ (torsion F d) b‖ := norm_nonneg _
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (Fintype.card F) := Real.sqrt_nonneg _
  -- `0 ≤ x < √q ⟹ x² < (√q)² = q`
  have hsq : ‖eta ψ (torsion F d) b‖ ^ 2 < (Real.sqrt (Fintype.card F)) ^ 2 := by
    have := mul_lt_mul'' hlt hlt hnn hnn
    simpa [pow_two] using this
  have hqnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  rwa [Real.sq_sqrt hqnn] at hsq

end ArkLib.ProximityGap.PrizeStructuralConstant

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.PrizeStructuralConstant.prizeRadiusSq_torsion_le
#print axioms ArkLib.ProximityGap.PrizeStructuralConstant.prizeRadiusSq_torsion_lt_card
