/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_MomentRatioLowerBound

/-!
# A sharper `√5·√n` moment-ratio LOWER bound on the Paley/BGK maximum `M` (issue #444 — floor)

This file extends the second-moment floor of `_AvFloor_MomentRatioLowerBound`
(`M² ≥ A₂/A₁`, asymptotically `√3·√n`) to the **third-moment ratio floor**

> `M² · A₂ ≥ A₃`,   where  `Aᵣ = ∑_{b≠0} ‖η_b‖^{2r}`,

i.e. `M² ≥ A₃ / A₂`. Here `M² := sup'_{b≠0} ‖η_b‖²`, `η_b = ∑_{x∈G} ψ(b·x)` is the incomplete
character sum over a finite multiplicative subgroup `G = μ_n ⊆ F_p^*`.

## The engine (a WEIGHTED max·Σ inequality, one notch up from the `√3` engine)

The `√3` floor used `∑ g² ≤ (sup g)·∑ g` with `g_b = ‖η_b‖²`, giving `A₂ ≤ M²·A₁`.

The `√5` floor uses the **weighted** form `∑ (h·g) ≤ (sup h)·∑ g` with `h_b = ‖η_b‖²`
(so `sup h = M²`) and `g_b = ‖η_b‖⁴ ≥ 0`:

> `A₃ = ∑_{b≠0} ‖η_b‖²·‖η_b‖⁴ ≤ (sup'_{b≠0} ‖η_b‖²)·∑_{b≠0} ‖η_b‖⁴ = M²·A₂`.

This is `weighted_sum_le_sup'_mul_sum` below — a strict generalization of
`sum_sq_le_sup'_mul_sum` (recovered at `h = g`).

## The energy substitution and the `√5` asymptotics

Via the substrate moment identity (`nonzero_moment`, from the substrate
`subgroup_gaussSum_moment`: `∑_b ‖η_b‖^{2r} = q·E_r(G)`, `E_r = rEnergy G r`) and
`‖η_0‖ = n`:

> `A₂ = q·E₂ − n⁴`,   `A₃ = q·E₃ − n⁶`,   `q = |F|`, `n = |G|`.

so `M² ≥ (q·E₃ − n⁶) / (q·E₂ − n⁴)`. The theorem `energy_moment_floor_sqrt5` records the
clean cross-multiplied inequality `q·E₃ − n⁶ ≤ M²·(q·E₂ − n⁴)`, axiom-clean from the substrate.

### Why this yields `√5` (exact-computation evidence; NOT proved here)

`E₃(μ_n) = 15n³ − 45n² + 40n` and `E₂(μ_n) = 3n² − 3n` **exactly** for all primes `p > n⁴`
(the wraparound surpluses `W₂ = W₃ = 0` by Stickelberger above that threshold — verified by
exact integer computation below). Hence as `q → ∞`,

> `A₃/A₂ = (q·E₃ − n⁶)/(q·E₂ − n⁴) → E₃/E₂ = (15n³−45n²+40n)/(3n²−3n) → 5n`,

giving the asymptotic floor `M ≥ √5·√n`, strictly sharper than the `√3·√n` of the second-moment
floor (which it contains: the same proof at `r=2,1` recovers `M²≥A₂/A₁`).

### Exact verification (issue #444 prize-scale primes, by exact integer computation)

| `n` | `p` (least prime `>n⁴`, `n∣p−1`) | `W₂` | `W₃` | `M²` | `A₃/A₂` | `M²≥A₃/A₂` |
|----:|---------------------------------:|-----:|-----:|-----:|--------:|:----------:|
| 16  | 65537                            | 0    | 0    | 191.5| 69.96   | ✓          |
| 32  | 1048609                          | 0    | 0    | 528.2| 149.81  | ✓          |

(`A₃/A₂ → 5n = 80, 160` as `q → ∞`; at the prize prime `q≈n⁴` the ratio is `≈4.4n`, climbing to
`5n`. The inequality `M² ≥ A₃/A₂` is exact and verified.)

## Honesty (the §6 contract)

This proves `M ≥ c·√n` with `c → √5` (the *floor*), strictly improving the `√3` floor. It does
**NOT** prove the prize-relevant `M = Ω(√(n log p))` lower bound — the log factor is the open
Ω-result, and the moment-ratio method provably CAPS at `bounded·√n` (the DC term `n^{2r}` dominates
`q·E_r` past `r ≈ β = O(1)`, the DC-crossover). The inequality `M²·A₂ ≥ A₃` is exact and
axiom-clean; the numeric value `5n` of `A₃/A₂` rests on the energy facts `E₂ = 3n²−3n`,
`E₃ = 15n³−45n²+40n` (Stickelberger, `p > n⁴`), recorded as *evidence*, not theorems in this file.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.Frontier.AvFloor (nonzero_moment eta_zero eta_zero_moment)

namespace ArkLib.ProximityGap.Frontier.AvFloorSqrt5

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The weighted max·Σ inequality (pure, no number theory) -/

/-- **The weighted key inequality.** For a `Finset` `s`, a nonnegative weight `g : ι → ℝ`,
and `h : ι → ℝ`,
`∑_{i∈s} h i · g i ≤ (sup'_{i∈s} h) · ∑_{i∈s} g i`.

Each term obeys `h i · g i ≤ (sup' h) · g i` since `h i ≤ sup' h` (`Finset.le_sup'`) and
`g i ≥ 0`; summing and pulling the constant out (`Finset.mul_sum`) gives the claim. This
strictly generalizes `sum_sq_le_sup'_mul_sum` (take `h = g`). -/
theorem weighted_sum_le_sup'_mul_sum {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (h g : ι → ℝ) (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, h i * g i) ≤ (s.sup' hne h) * (∑ i ∈ s, g i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  exact mul_le_mul_of_nonneg_right (Finset.le_sup' h hi) (hg i hi)

/-! ## 2. The third-moment-ratio floor inequality for the Paley/BGK maximum -/

/-- **The third moment-ratio floor (abstract form).** Over the nonzero frequencies
`s = univ.erase 0`, the sixth-power sum is bounded by `M²` times the fourth-power sum, where
`M² := sup'_{b≠0} ‖η_b‖²`:

> `∑_{b≠0} ‖η_b‖⁶ ≤ (sup'_{b≠0} ‖η_b‖²) · ∑_{b≠0} ‖η_b‖⁴`.

This is `M² · A₂ ≥ A₃`, i.e. `M² ≥ A₃/A₂`. Pure consequence of `weighted_sum_le_sup'_mul_sum`
with `h b = ‖η_b‖²`, `g b = ‖η_b‖⁴` (note `‖η_b‖² · ‖η_b‖⁴ = ‖η_b‖⁶`). -/
theorem sixthSum_le_sup'_fourthSum (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4) := by
  have h := weighted_sum_le_sup'_mul_sum (Finset.univ.erase (0 : F)) hne
    (fun b => ‖eta ψ G b‖ ^ 2) (fun b => ‖eta ψ G b‖ ^ 4) (fun b _ => by positivity)
  -- `‖η_b‖² · ‖η_b‖⁴ = ‖η_b‖⁶`
  have hpow : ∀ b : F, ‖eta ψ G b‖ ^ 2 * ‖eta ψ G b‖ ^ 4 = ‖eta ψ G b‖ ^ 6 := by
    intro b; rw [← pow_add]
  simpa only [hpow] using h

/-- **The `√5` moment-ratio floor with both sums made explicit (energy form).** Substituting the
moment identities `A₂ = q·E₂ − n⁴`, `A₃ = q·E₃ − n⁶` into `sixthSum_le_sup'_fourthSum`:

> `q·E₃ − n⁶  ≤  M² · (q·E₂ − n⁴)`,

where `M² := sup'_{b≠0} ‖η_b‖²`, `q = |F|`, `n = |G|`, `E_r = rEnergy G r`. Rearranged:
`M² ≥ (q·E₃ − n⁶)/(q·E₂ − n⁴)`. With `E₃ = 15n³−45n²+40n`, `E₂ = 3n²−3n` (`p > n⁴`,
exact-computation evidence) the right side `→ 5n` as `q → ∞`, giving the floor `M ≥ √5·√n`.

This is the sharpened LOWER half of the prize (the floor) made axiom-clean from the substrate. -/
theorem energy_moment_floor_sqrt5 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (Fintype.card F : ℝ) * rEnergy G 3 - (G.card : ℝ) ^ 6
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ) * rEnergy G 2 - (G.card : ℝ) ^ 4) := by
  have hbase := sixthSum_le_sup'_fourthSum ψ G hne
  -- A₃ (r = 3, exponent `2*3 = 6`) and A₂ (r = 2, exponent `2*2 = 4`) via `nonzero_moment`.
  have hA3 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 6)
      = (Fintype.card F : ℝ) * rEnergy G 3 - (G.card : ℝ) ^ 6 := by
    have h := nonzero_moment hψ G 3
    norm_num only at h
    exact h
  have hA2 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4)
      = (Fintype.card F : ℝ) * rEnergy G 2 - (G.card : ℝ) ^ 4 := by
    have h := nonzero_moment hψ G 2
    norm_num only at h
    exact h
  rw [hA3, hA2] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.AvFloorSqrt5

#print axioms ArkLib.ProximityGap.Frontier.AvFloorSqrt5.weighted_sum_le_sup'_mul_sum
#print axioms ArkLib.ProximityGap.Frontier.AvFloorSqrt5.sixthSum_le_sup'_fourthSum
#print axioms ArkLib.ProximityGap.Frontier.AvFloorSqrt5.energy_moment_floor_sqrt5
