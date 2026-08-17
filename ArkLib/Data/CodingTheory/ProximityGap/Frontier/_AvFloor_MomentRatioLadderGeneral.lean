/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_SqrtSevenMomentRatio

/-!
# The GENERAL `r` moment-ratio floor ladder `M² · Aᵣ ≥ Aᵣ₊₁` (issue #444 — floor capstone)

The individual rungs of the moment-ratio floor — `√3·√n` (r=2,
`_AvFloor_MomentRatioLowerBound.energy_moment_floor`), `√5·√n` (r=3,
`_AvFloor_SqrtFiveMomentRatio.energy_moment_floor_sqrt5`), `√7·√n` (r=4,
`_AvFloor_SqrtSevenMomentRatio.energy_moment_floor_sqrt7`) — are all SPECIAL CASES of one
parametrized inequality. This file states and proves that inequality **for every `r : ℕ` at once**,
giving the citable capstone of the floor ladder.

## The ladder, in one theorem

For `Aᵣ := ∑_{b≠0} ‖η_b‖^{2r}` and `M² := sup'_{b≠0} ‖η_b‖²`:

> `Aᵣ₊₁ ≤ M² · Aᵣ`   for every `r : ℕ`,   i.e.   `M² ≥ Aᵣ₊₁ / Aᵣ`.

Proof: the weighted max·Σ engine `weighted_sum_le_sup'_mul_sum` with `h_b = ‖η_b‖²`
(so `sup h = M²`) and `g_b = ‖η_b‖^{2r} ≥ 0`, using `‖η_b‖² · ‖η_b‖^{2r} = ‖η_b‖^{2(r+1)}`.

## The energy form, in one theorem

Substituting the substrate identity `Aᵣ = q·Eᵣ − n^{2r}` (`nonzero_moment`, general `r`) at `r+1`
and `r`:

> `q·Eᵣ₊₁ − n^{2(r+1)}  ≤  M² · (q·Eᵣ − n^{2r})`   for every `r : ℕ`,

where `q = |F|`, `n = |G|`, `Eᵣ = rEnergy G r`. As `q → ∞` the ratio `→ Eᵣ₊₁/Eᵣ`, which on the
thin subgroup `μ_n` tends to `(2r+1)·n` (double-factorial substrate `Eᵣ ~ (2r−1)!!·nʳ`), giving the
floor `M ≥ √(2r+1)·√n`. The numeric `√(2r+1)` is bounded by the DC-crossover at `r₀~5` (beyond which
the `n^{2r}` subtraction dominates `q·Eᵣ`), so the ladder does NOT yield an unbounded floor — this is
the documented reason the floor saturates at `√(bounded)·√n` and does NOT by itself reach the
conjectured `√(n·log(p/n))`. The individual rungs `r = 2, 3, 4` below the cap recover
`√3, √5, √7` respectively.

This is a LOWER bound (the floor). It does NOT close CORE (an UPPER bound): it certifies that the
honest value `M` is at least `√(2r+1)·√n` for any `r` below the DC cap, but cannot exceed the cap.
-/

set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.AvFloorLadder

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.Frontier.AvFloor (nonzero_moment eta_zero eta_zero_moment)
open ArkLib.ProximityGap.Frontier.AvFloorSqrt5 (weighted_sum_le_sup'_mul_sum)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The general moment-ratio floor (abstract form), every `r` at once.** Over the nonzero
frequencies `s = univ.erase 0`, the `(2r+2)`-power sum is bounded by `M²` times the `2r`-power sum,
where `M² := sup'_{b≠0} ‖η_b‖²`:

> `∑_{b≠0} ‖η_b‖^{2(r+1)} ≤ (sup'_{b≠0} ‖η_b‖²) · ∑_{b≠0} ‖η_b‖^{2r}`.

This is `M² · Aᵣ ≥ Aᵣ₊₁`, i.e. `M² ≥ Aᵣ₊₁/Aᵣ`, for EVERY `r : ℕ`. Pure consequence of
`weighted_sum_le_sup'_mul_sum` with `h b = ‖η_b‖²`, `g b = ‖η_b‖^{2r}` (note
`‖η_b‖² · ‖η_b‖^{2r} = ‖η_b‖^{2(r+1)}`). Specializes to `sixthSum_le_sup'_fourthSum` (r=2) and
`eighthSum_le_sup'_sixthSum` (r=3). -/
theorem momentSucc_le_sup'_moment (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * (r + 1)))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)) := by
  have h := weighted_sum_le_sup'_mul_sum (Finset.univ.erase (0 : F)) hne
    (fun b => ‖eta ψ G b‖ ^ 2) (fun b => ‖eta ψ G b‖ ^ (2 * r)) (fun b _ => by positivity)
  -- `‖η_b‖² · ‖η_b‖^{2r} = ‖η_b‖^{2(r+1)}`
  have hpow : ∀ b : F, ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ (2 * r) = ‖eta ψ G b‖ ^ (2 * (r + 1)) := by
    intro b
    rw [← pow_add]
    congr 1
    ring
  simpa only [hpow] using h

/-- **The general moment-ratio floor (energy form), every `r` at once.** Substituting the substrate
moment identities `Aᵣ₊₁ = q·Eᵣ₊₁ − n^{2(r+1)}`, `Aᵣ = q·Eᵣ − n^{2r}` (`nonzero_moment`) into
`momentSucc_le_sup'_moment`:

> `q·Eᵣ₊₁ − n^{2(r+1)}  ≤  M² · (q·Eᵣ − n^{2r})`   for EVERY `r : ℕ`,

where `M² := sup'_{b≠0} ‖η_b‖²`, `q = |F|`, `n = |G|`, `Eᵣ = rEnergy G r`. Rearranged:
`M² ≥ (q·Eᵣ₊₁ − n^{2(r+1)})/(q·Eᵣ − n^{2r})`. This is the parametrized capstone of the floor ladder;
the rungs `r = 1, 2, 3` recover the `√3, √5, √7` floors. UNCONDITIONAL: holds for any `G`,
regardless of the `Eᵣ` values. -/
theorem energy_moment_floor_general {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (Fintype.card F : ℝ) * rEnergy G (r + 1) - (G.card : ℝ) ^ (2 * (r + 1))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r)) := by
  have hbase := momentSucc_le_sup'_moment ψ G hne r
  have hAsucc := nonzero_moment hψ G (r + 1)
  have hAr := nonzero_moment hψ G r
  rw [hAsucc, hAr] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.AvFloorLadder

#print axioms ArkLib.ProximityGap.Frontier.AvFloorLadder.momentSucc_le_sup'_moment
#print axioms ArkLib.ProximityGap.Frontier.AvFloorLadder.energy_moment_floor_general
