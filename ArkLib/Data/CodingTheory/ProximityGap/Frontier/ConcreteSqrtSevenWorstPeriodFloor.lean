/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_SqrtSevenMomentRatio
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_MomentRatioLadderGeneral
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly

/-!
# Wiring the `√7` moment-ratio floor onto the CONCRETE worst period (#444 — floor connective)

`_AvFloor_SqrtSevenMomentRatio` proved the abstract fourth moment-ratio floor

> `energy_moment_floor_sqrt7 : q·E₄ − n⁸  ≤  (sup'_{b≠0} ‖η_b‖²) · (q·E₃ − n⁶)`,

i.e. `M² ≥ (q·E₄ − n⁸)/(q·E₃ − n⁶)` where `M² = sup'_{b≠0} ‖η_b‖²`. The Shaw-value bridge and the
concrete corridor, however, are stated over the canonical concrete object
`worstPeriod ψ G hne = max_{b≠0} ‖η_b‖` (a sup' of the NORM, not the squared norm). The two are equal
(`x ↦ x²` is monotone on `≥0`, so the squared sup' is the sup' of the square), but nothing in-tree had
discharged that identity, so the sharpened `√7` floor was NOT yet available on `worstPeriod`.

This file supplies the missing connective rung:

> `worstPeriod_sq_eq_sup'_sq`               : `(worstPeriod ψ G hne)² = sup'_{b≠0} ‖η_b‖²`,
> `worstPeriod_sq_moment_ratio_floor`       : `q·E₄ − n⁸ ≤ (worstPeriod ψ G hne)² · (q·E₃ − n⁶)`,
> `worstPeriod_sq_moment_ratio_floor_general`: `q·Eᵣ₊₁ − n^{2(r+1)} ≤ (worstPeriod ψ G hne)² · (q·Eᵣ − n^{2r})` ∀ r.

The second is the abstract `√7` floor transported verbatim onto the concrete worst period (the `r = 3`
rung); the third is the FULL parametrized ladder `energy_moment_floor_general` transported the same
way, so the entire `√3, √5, √7, …` floor ladder lives on `worstPeriod` at once. The SHARPENED lower
bound (`M² ≥ (q·Eᵣ₊₁−n^{2(r+1)})/(q·Eᵣ−n^{2r})`, the `r = 3` rung asymptotically `→ 7n`) now lives on the
exact object the Shaw-value normalization consumes, strictly stronger than the RMS `n(q−n)/(q−1)` floor
already wired there (`ConcreteParsevalLower.worstPeriod_sq_ge_parseval`).

## Honesty (the prize is the GAP, untouched)

Pure Lane-2 INSTANTIATION/transport: it equates two already-defined sup' objects and re-exports a
PROVEN abstract floor on the concrete one. It adds NO analytic content — no anti-concentration, no
cancellation, no completion, no NEW moment, no capacity claim. This is a LOWER bound (the floor); it
sharpens the honest-value gap, it does NOT close CORE. CORE `M(μ_n) ≤ C·√(n·log(p/n))` (an UPPER
bound) stays OPEN. The `→ 7n` value remains asymptotic computational evidence (see the parent file's
honesty note); the Lean statement is the exact substrate inequality `q·E₄ − n⁸ ≤ M²·(q·E₃ − n⁶)`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.Frontier.AvFloorSqrt7 (energy_moment_floor_sqrt7)
open ArkLib.ProximityGap.Frontier.AvFloorLadder (energy_moment_floor_general)
open ProximityGap.Frontier.ConcreteMomentAssembly (worstPeriod worstPeriod_nonneg)

namespace ProximityGap.Frontier.ConcreteSqrtSevenWorstPeriodFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Squared worst period is the sup' of the squared norms.** `(max_{b≠0}‖η_b‖)² = max_{b≠0}‖η_b‖²`.
The `x ↦ x²` map is monotone on `≥0`, so squaring commutes with the (nonempty) sup' over the nonzero
frequencies. Proved by extracting the argmax `b₀` of `‖η_·‖`: it is also the argmax of `‖η_·‖²`
(squaring is monotone on `≥0`), so both sides equal `‖η_{b₀}‖²`. -/
theorem worstPeriod_sq_eq_sup'_sq (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (worstPeriod ψ G hne) ^ 2
      = (Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2) := by
  -- `worstPeriod` is the sup' over `nonzeroFreqs F = univ.erase 0`; align the carrier set.
  have hwp : worstPeriod ψ G hne
      = (Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖) := by
    unfold worstPeriod ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs; rfl
  -- argmax `b₀` of the NORM realises the worst period.
  obtain ⟨b₀, hb₀, hmax⟩ :=
    (Finset.univ.erase (0 : F)).exists_mem_eq_sup' hne (fun b => ‖eta ψ G b‖)
  -- LHS = ‖η_{b₀}‖²
  have hL : (worstPeriod ψ G hne) ^ 2 = ‖eta ψ G b₀‖ ^ 2 := by
    rw [hwp, hmax]
  -- RHS = ‖η_{b₀}‖²: b₀ also maximises the SQUARE (squaring monotone on ≥0).
  have hR : (Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2)
      = ‖eta ψ G b₀‖ ^ 2 := by
    apply le_antisymm
    · -- every squared term ≤ ‖η_{b₀}‖²
      apply Finset.sup'_le
      intro b hb
      have hle : ‖eta ψ G b‖ ≤ ‖eta ψ G b₀‖ := by
        have : ‖eta ψ G b‖ ≤ (Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖) :=
          Finset.le_sup' (fun b => ‖eta ψ G b‖) hb
        rwa [hmax] at this
      have hnn : (0 : ℝ) ≤ ‖eta ψ G b‖ := norm_nonneg _
      nlinarith [hnn, hle, norm_nonneg (eta ψ G b₀)]
    · -- ‖η_{b₀}‖² ≤ the sup' (single member)
      exact Finset.le_sup' (fun b => ‖eta ψ G b‖ ^ 2) hb₀
  rw [hL, hR]

/-- **Concrete `√7` moment-ratio floor on the worst period.** Transport of the abstract floor
`energy_moment_floor_sqrt7` onto `worstPeriod` via `worstPeriod_sq_eq_sup'_sq`:

> `q·E₄ − n⁸  ≤  (worstPeriod ψ G hne)² · (q·E₃ − n⁶)`,

i.e. `M(μ_n)² ≥ (q·E₄ − n⁸)/(q·E₃ − n⁶)`. The sharpened LOWER bound (asymptotically `→ 7n`, see the
parent honesty note) is now stated on the canonical concrete worst period the Shaw-value bridge
consumes — strictly stronger than the wired RMS Parseval floor `n(q−n)/(q−1) ≤ M²`. FLOOR only; does
NOT close CORE. -/
theorem worstPeriod_sq_moment_ratio_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (Fintype.card F : ℝ) * rEnergy G 4 - (G.card : ℝ) ^ 8
      ≤ (worstPeriod ψ G hne) ^ 2
          * ((Fintype.card F : ℝ) * rEnergy G 3 - (G.card : ℝ) ^ 6) := by
  have habs := energy_moment_floor_sqrt7 hψ G hne
  rw [worstPeriod_sq_eq_sup'_sq ψ G hne]
  exact habs

/-- **Concrete GENERAL moment-ratio floor on the worst period — every rung at once.** Transport of
the proven parametrized abstract ladder `energy_moment_floor_general` onto `worstPeriod` via
`worstPeriod_sq_eq_sup'_sq`:

> `q·Eᵣ₊₁ − n^{2(r+1)}  ≤  (worstPeriod ψ G hne)² · (q·Eᵣ − n^{2r})`   for EVERY `r : ℕ`,

i.e. `M(μ_n)² ≥ (q·Eᵣ₊₁ − n^{2(r+1)})/(q·Eᵣ − n^{2r})`. The rungs `r = 1, 2, 3` recover the concrete
`√3, √5, √7` floors; `worstPeriod_sq_moment_ratio_floor` above is the `r = 3` specialization. The
WHOLE floor ladder is now available on the canonical concrete worst period the Shaw-value bridge
consumes — strictly subsuming the single-rung transport and the RMS Parseval floor. UNCONDITIONAL
(holds for any `G`). FLOOR only; does NOT close CORE. -/
theorem worstPeriod_sq_moment_ratio_floor_general {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (Fintype.card F : ℝ) * rEnergy G (r + 1) - (G.card : ℝ) ^ (2 * (r + 1))
      ≤ (worstPeriod ψ G hne) ^ 2
          * ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)) := by
  have habs := energy_moment_floor_general hψ G hne r
  rw [worstPeriod_sq_eq_sup'_sq ψ G hne]
  exact habs

end ProximityGap.Frontier.ConcreteSqrtSevenWorstPeriodFloor

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.ConcreteSqrtSevenWorstPeriodFloor.worstPeriod_sq_eq_sup'_sq
#print axioms ProximityGap.Frontier.ConcreteSqrtSevenWorstPeriodFloor.worstPeriod_sq_moment_ratio_floor
#print axioms ProximityGap.Frontier.ConcreteSqrtSevenWorstPeriodFloor.worstPeriod_sq_moment_ratio_floor_general
