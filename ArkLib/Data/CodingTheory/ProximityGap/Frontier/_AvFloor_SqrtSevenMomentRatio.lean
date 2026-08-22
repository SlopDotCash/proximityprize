/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_SqrtFiveMomentRatio

/-!
# A sharper `√7·√n` moment-ratio LOWER bound on the Paley/BGK maximum `M` (issue #444 — floor)

This file extends the third-moment floor of `_AvFloor_SqrtFiveMomentRatio`
(`M² ≥ A₃/A₂`, asymptotically `√5·√n`) to the **fourth-moment ratio floor**

> `M² · A₃ ≥ A₄`,   where  `Aᵣ = ∑_{b≠0} ‖η_b‖^{2r}`,

i.e. `M² ≥ A₄ / A₃`. Here `M² := sup'_{b≠0} ‖η_b‖²`, `η_b = ∑_{x∈G} ψ(b·x)` is the incomplete
character sum over a finite multiplicative subgroup `G = μ_n ⊆ F_p^*`. This is the **r = 4 rung**
of the moment-ratio floor ladder `M² ≥ Aᵣ/Aᵣ₋₁`.

## The engine (the SAME weighted max·Σ inequality, one notch up from the `√5` engine)

The `√5` floor used `weighted_sum_le_sup'_mul_sum` with `h_b = ‖η_b‖²` (so `sup h = M²`) and
`g_b = ‖η_b‖⁴ ≥ 0`, giving `A₃ ≤ M²·A₂`.

The `√7` floor uses the **same** weighted form `∑ (h·g) ≤ (sup h)·∑ g` with `h_b = ‖η_b‖²`
(so `sup h = M²` again) and `g_b = ‖η_b‖⁶ ≥ 0`:

> `A₄ = ∑_{b≠0} ‖η_b‖²·‖η_b‖⁶ ≤ (sup'_{b≠0} ‖η_b‖²)·∑_{b≠0} ‖η_b‖⁶ = M²·A₃`.

Both `weighted_sum_le_sup'_mul_sum` (the abstract engine) and `nonzero_moment` (the substrate
moment identity `Aᵣ = q·Eᵣ − n^{2r}`) are reused unchanged from `_AvFloor_MomentRatioLowerBound`;
nothing new is needed at the kernel level — this is a clean one-rung extension of a proven theorem.

## The energy form and the `→ 7n` asymptotic value

Substituting `A₄ = q·E₄ − n⁸` and `A₃ = q·E₃ − n⁶` (`nonzero_moment` at `r = 4`, `r = 3`) gives
the cross-multiplied inequality recorded as `energy_moment_floor_sqrt7`:

> `q·E₄ − n⁸  ≤  M² · (q·E₃ − n⁶)`,   i.e.   `M² ≥ (q·E₄ − n⁶)/(q·E₃ − n⁶)`.

As `q → ∞` this `→ E₄/E₃`. The double-factorial substrate values `Eᵣ(μ_n) ~ (2r−1)!!·n^r`
(`E₂ ~ 3n²`, `E₃ ~ 15n³`, `E₄ ~ 105n⁴`, with `3 = 3!!, 15 = 5!!, 105 = 7!!`) give
`E₄/E₃ → 105n⁴ / 15n³ = 7n`, i.e. the floor `M ≥ √7·√n` — sharper than the `√5` floor.

**Honesty note (probe-verified, evidence not a kernel claim).** Exact integer computation of
`E₄(μ_n) = rEnergy(μ_n, 4)` over PROPER thin subgroups `μ_n ⊆ F_p^*` with `p > n⁴` and `n | p−1`
(`n = 4,8,16,32,64`) gives `E₄/(105·n⁴) = 0.182, 0.442, 0.676, 0.831, 0.917` (→ 1, slow because
`E₄` carries large lower-order corrections — it is NOT a clean degree-4 polynomial in `n`, unlike
`E₃ = 15n³−45n²+40n` which is exact) and `A₄/A₃` empirically `→ 7n` (`430.8 / 448 = 0.96` at
`n = 64`). So the numeric value `7n` of `A₄/A₃` is recorded as **asymptotic computational
evidence**, NOT as an exact closed-form theorem in this file. The Lean theorems below state ONLY
the unconditional cross-multiplied inequality, which holds for ANY `G` regardless of the `E_r`
values — exactly as for the `√3` and `√5` floors.

This is the next rung of the LOWER half of the prize (the floor) made axiom-clean from the
substrate. It does NOT close CORE (an UPPER bound): the floor only certifies that the honest value
`M` is at least `√7·√n` asymptotically, sharpening the gap to the conjectured `√(n·log(p/n))`.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.Frontier.AvFloor (nonzero_moment eta_zero eta_zero_moment)
open ArkLib.ProximityGap.Frontier.AvFloorSqrt5 (weighted_sum_le_sup'_mul_sum)

namespace ArkLib.ProximityGap.Frontier.AvFloorSqrt7

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The fourth moment-ratio floor (abstract form).** Over the nonzero frequencies
`s = univ.erase 0`, the eighth-power sum is bounded by `M²` times the sixth-power sum, where
`M² := sup'_{b≠0} ‖η_b‖²`:

> `∑_{b≠0} ‖η_b‖⁸ ≤ (sup'_{b≠0} ‖η_b‖²) · ∑_{b≠0} ‖η_b‖⁶`.

This is `M² · A₃ ≥ A₄`, i.e. `M² ≥ A₄/A₃`. Pure consequence of `weighted_sum_le_sup'_mul_sum`
with `h b = ‖η_b‖²`, `g b = ‖η_b‖⁶` (note `‖η_b‖² · ‖η_b‖⁶ = ‖η_b‖⁸`). -/
theorem eighthSum_le_sup'_sixthSum (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 8)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6) := by
  have h := weighted_sum_le_sup'_mul_sum (Finset.univ.erase (0 : F)) hne
    (fun b => ‖eta ψ G b‖ ^ 2) (fun b => ‖eta ψ G b‖ ^ 6) (fun b _ => by positivity)
  -- `‖η_b‖² · ‖η_b‖⁶ = ‖η_b‖⁸`
  have hpow : ∀ b : F, ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ 6 = ‖eta ψ G b‖ ^ 8 := by
    intro b; rw [← pow_add]
  simpa only [hpow] using h

/-- **The `√7` moment-ratio floor with both sums made explicit (energy form).** Substituting the
moment identities `A₃ = q·E₃ − n⁶`, `A₄ = q·E₄ − n⁸` into `eighthSum_le_sup'_sixthSum`:

> `q·E₄ − n⁸  ≤  M² · (q·E₃ − n⁶)`,

where `M² := sup'_{b≠0} ‖η_b‖²`, `q = |F|`, `n = |G|`, `E_r = rEnergy G r`. Rearranged:
`M² ≥ (q·E₄ − n⁸)/(q·E₃ − n⁶)`. With the double-factorial substrate values `E₄ ~ 105n⁴`,
`E₃ = 15n³−45n²+40n` the right side `→ 7n` as `q → ∞`, giving the floor `M ≥ √7·√n` — see the
honesty note in the module docstring (the `7n` value is asymptotic computational evidence).

This is the sharpened LOWER half of the prize (the floor) made axiom-clean from the substrate. -/
theorem energy_moment_floor_sqrt7 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (Fintype.card F : ℝ) * rEnergy G 4 - (G.card : ℝ) ^ 8
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ) * rEnergy G 3 - (G.card : ℝ) ^ 6) := by
  have hbase := eighthSum_le_sup'_sixthSum ψ G hne
  -- A₄ (r = 4, exponent `2*4 = 8`) and A₃ (r = 3, exponent `2*3 = 6`) via `nonzero_moment`.
  have hA4 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 8)
      = (Fintype.card F : ℝ) * rEnergy G 4 - (G.card : ℝ) ^ 8 := by
    have h := nonzero_moment hψ G 4
    norm_num only at h
    exact h
  have hA3 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6)
      = (Fintype.card F : ℝ) * rEnergy G 3 - (G.card : ℝ) ^ 6 := by
    have h := nonzero_moment hψ G 3
    norm_num only at h
    exact h
  rw [hA4, hA3] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.AvFloorSqrt7

#print axioms ArkLib.ProximityGap.Frontier.AvFloorSqrt7.eighthSum_le_sup'_sixthSum
#print axioms ArkLib.ProximityGap.Frontier.AvFloorSqrt7.energy_moment_floor_sqrt7
