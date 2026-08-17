/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# A moment-ratio LOWER bound on the Paley/BGK maximum `M` (issue #444 — the "floor")

With `η_b = ∑_{x∈G} ψ(b·x)` the incomplete character sum over a finite multiplicative subgroup
`G = μ_n ⊆ F_p^*`, and `M = max_{b≠0} ‖η_b‖`, this file proves the elementary **second-moment
ratio lower bound**

> `M² · A₁ ≥ A₂`,   where  `A₁ = ∑_{b≠0} ‖η_b‖²`,  `A₂ = ∑_{b≠0} ‖η_b‖⁴`,

i.e. `M² ≥ A₂ / A₁`. The engine is the pure max·Σ ≥ Σ² inequality
`∑ g² ≤ (sup' g) · ∑ g` applied to `g b = ‖η_b‖²` over the nonzero frequencies.

Combining with the substrate moment identity
`subgroup_gaussSum_moment` (`∑_b ‖η_b‖^{2r} = q · E_r(G)`, `E_r = rEnergy G r`) and the value
`‖η_0‖ = |G| = n` of the trivial frequency, the two sums become

> `A₁ = q·E₁ − n²`   and   `A₂ = q·E₂ − n⁴`,   `q = |F|`, `n = |G|`,

so `M² ≥ (q·E₂ − n⁴) / (q·E₁ − n²) = (q·E₂ − n⁴) / (q·n − n²)` (using `E₁ = n`).

## Exact-computation evidence (verified by exact integer computation; NOT proved here)

* `E₂(μ_n) = 3n² − 3n` exactly for all primes `p > n⁴` (the wraparound surplus `W₂ = 0` by
  Stickelberger above that threshold). Hence `A₂/A₁ = (q(3n²−3n) − n⁴)/(qn − n²) → 3n` as
  `q → ∞`, giving the asymptotic floor `M ≥ √3 · √n`.
* The **unconditional** clean floor uses only the diagonal-quadruple lower bound
  `E₂ ≥ 2n² − n` (the `(v,w)` pairs with `{v}` a permutation of `{w}` already give this),
  whence `A₂/A₁ ≥ (q(2n²−n) − n⁴)/(qn − n²) → 2n`, i.e. `M ≥ √2 · √n` — strictly beating the
  trivial Parseval floor `√n`.

## Honesty (the §6 contract)

This proves `M ≥ c·√n` with a constant `c > 1` (the *floor*). It does **NOT** prove the prize-
relevant `M = Ω(√(n log p))` lower bound — the log factor is the open Ω-result. The inequality
`M² · A₁ ≥ A₂` is exact and axiom-clean; the numeric values `2n` / `3n` of `A₂/A₁` quoted above
rest on the energy facts `E₂ ≥ 2n²−n` (diagonal) and `E₂ = 3n²−3n` (Stickelberger, `p > n⁴`),
which are recorded as *evidence*, not theorems in this file.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)

namespace ArkLib.ProximityGap.Frontier.AvFloor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The abstract max·Σ ≥ Σ² inequality (pure, no number theory) -/

/-- **The key inequality.** For a nonempty `Finset` `s` and `g : ι → ℝ` nonnegative on `s`,
the sum of squares is bounded by the maximum times the sum:
`∑_{i∈s} g i² ≤ (sup'_{i∈s} g) · ∑_{i∈s} g i`.

Each term obeys `g i² = g i · g i ≤ (sup' g) · g i` since `g i ≤ sup' g` (`Finset.le_sup'`)
and `g i ≥ 0`; summing and pulling the constant out (`Finset.mul_sum`) gives the claim. -/
theorem sum_sq_le_sup'_mul_sum {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (g : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ i ∈ s, g i ^ 2) ≤ (s.sup' hne g) * (∑ i ∈ s, g i) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [pow_two]
  exact mul_le_mul_of_nonneg_right (Finset.le_sup' g hi) (hg i hi)

/-! ## 2. The main floor inequality for the Paley/BGK maximum -/

/-- **The moment-ratio floor (abstract form).** Over the nonzero frequencies
`s = univ.erase 0`, the fourth-power sum is bounded by `M²` times the square sum, where
`M² := sup'_{b≠0} ‖η_b‖²`:

> `∑_{b≠0} ‖η_b‖⁴ ≤ (sup'_{b≠0} ‖η_b‖²) · ∑_{b≠0} ‖η_b‖²`.

This is `M² · A₁ ≥ A₂`, i.e. `M² ≥ A₂/A₁`. Pure consequence of `sum_sq_le_sup'_mul_sum`
with `g b = ‖η_b‖²` (note `‖η_b‖⁴ = (‖η_b‖²)²`). -/
theorem fourthSum_le_sup'_sqSum (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2) := by
  have h := sum_sq_le_sup'_mul_sum (Finset.univ.erase (0 : F)) hne
    (fun b => ‖eta ψ G b‖ ^ 2) (fun b _ => by positivity)
  -- `(‖η_b‖²)² = ‖η_b‖⁴`
  simpa only [← pow_mul] using h

/-! ## 3. Splitting off the trivial frequency `b = 0` -/

/-- At `b = 0`: `η_0 = ∑_{x∈G} ψ(0·x) = ∑_{x∈G} ψ(0) = ∑_{x∈G} 1 = |G|`, so `‖η_0‖ = |G|`. -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  simp only [eta]
  simp [AddChar.map_zero_eq_one]

/-- The `b=0` term of the `2r`-moment is `‖η_0‖^{2r} = n^{2r}` (with `n = |G|`). -/
theorem eta_zero_moment (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    ‖eta ψ G 0‖ ^ (2 * r) = (G.card : ℝ) ^ (2 * r) := by
  rw [eta_zero]
  rw [Complex.norm_natCast]

/-- **The nonzero-frequency `2r`-moment via the substrate identity.**
`∑_{b≠0} ‖η_b‖^{2r} = q · E_r(G) − n^{2r}`, where `q = |F|`, `n = |G|`, `E_r = rEnergy G r`.

Proof: split `Finset.univ` into `{0} ∪ (univ.erase 0)` (`Finset.add_sum_erase`), use
`subgroup_gaussSum_moment` for the full sum and `eta_zero_moment` for the `b=0` term. -/
theorem nonzero_moment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r))
      = (Fintype.card F : ℝ) * rEnergy G r - (G.card : ℝ) ^ (2 * r) := by
  have hmem : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  have hsplit :
      ‖eta ψ G 0‖ ^ (2 * r) + (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r))
        = ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) :=
    Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ (2 * r)) hmem
  rw [eta_zero_moment] at hsplit
  rw [subgroup_gaussSum_moment hψ] at hsplit
  linarith

/-- **The moment-ratio floor with both sums made explicit (energy form).** Substituting the
moment identities `A₁ = q·E₁ − n²`, `A₂ = q·E₂ − n⁴` into `fourthSum_le_sup'_sqSum`:

> `q·E₂ − n⁴  ≤  M² · (q·E₁ − n²)`,

where `M² := sup'_{b≠0} ‖η_b‖²`, `q = |F|`, `n = |G|`, `E_r = rEnergy G r`. Rearranged:
`M² ≥ (q·E₂ − n⁴)/(q·E₁ − n²)`. With the substrate value `E₁ = n` the denominator is `q·n − n²`.

This is the LOWER half of the prize (the floor) made axiom-clean from the substrate. -/
theorem energy_moment_floor {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (Fintype.card F : ℝ) * rEnergy G 2 - (G.card : ℝ) ^ 4
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ) * rEnergy G 1 - (G.card : ℝ) ^ 2) := by
  have hbase := fourthSum_le_sup'_sqSum ψ G hne
  -- A₂ (r = 2, exponent `2*2 = 4`) and A₁ (r = 1, exponent `2*1 = 2`) via `nonzero_moment`.
  -- `nonzero_moment` produces exponents `2*r`; rewrite those to the literals `4`/`2` first,
  -- WITHOUT touching the `erase`-sum structure.
  have hA2 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4)
      = (Fintype.card F : ℝ) * rEnergy G 2 - (G.card : ℝ) ^ 4 := by
    have h := nonzero_moment hψ G 2
    norm_num only at h
    exact h
  have hA1 : (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2)
      = (Fintype.card F : ℝ) * rEnergy G 1 - (G.card : ℝ) ^ 2 := by
    have h := nonzero_moment hψ G 1
    norm_num only at h
    exact h
  rw [hA2, hA1] at hbase
  exact hbase

end ArkLib.ProximityGap.Frontier.AvFloor

#print axioms ArkLib.ProximityGap.Frontier.AvFloor.sum_sq_le_sup'_mul_sum
#print axioms ArkLib.ProximityGap.Frontier.AvFloor.fourthSum_le_sup'_sqSum
#print axioms ArkLib.ProximityGap.Frontier.AvFloor.eta_zero
#print axioms ArkLib.ProximityGap.Frontier.AvFloor.nonzero_moment
#print axioms ArkLib.ProximityGap.Frontier.AvFloor.energy_moment_floor
