/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumRawMoment
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# The period-spectrum power-sum law: `∑_{b≠0} η_bʳ = q·N₀(G,r) − nʳ` (#407)

The engine of the Gaussian-period moment law. `SubgroupGaussSumRawMoment.subgroup_gaussSum_rawMoment`
gives the all-frequency identity `∑_{b∈F} η_bʳ = q·N₀(G,r)`; subtracting the `b=0` term
`η_0 = |G| = n` (`GaussPeriodCosetReduction.eta_zero`) gives the **nonzero-spectrum** power sum

> `∑_{b≠0} η_bʳ = q·N₀(G,r) − nʳ`   for every `r` (odd included).

Since `η_b` is constant on each of the `m = (q−1)/n` `μ_n`-cosets of the nonzero frequencies
(`eta_mul_left`), this is `n·∑_i η_iʳ` over the `m` distinct Gaussian periods `η_i`, so it is exactly
the **period moment law** `∑_i η_iʳ = (q/n)·N₀(G,r) − n^{r−1}` (the consumer step that
`SubgroupGaussSumRawMoment` stated only in prose). It makes the per-frequency core (F2/F3) literally
equal to the additive-relation count `N₀` (F5/F6/F18) scaled by `q/n`, for all `r`.

Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.PeriodMomentLaw

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The nonzero-spectrum power-sum law** `∑_{b≠0} η_bʳ = q·N₀(G,r) − nʳ`, for every `r`. The engine
of the period moment law: divide by `n` (the coset multiplicity) to get `∑_i η_iʳ = (q/n)N₀ − n^{r−1}`
over the `m` distinct periods. -/
theorem rawMoment_erase_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b ^ r
      = (Fintype.card F : ℂ) * N0 G r - (G.card : ℂ) ^ r := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), subgroup_gaussSum_rawMoment hψ G r, eta_zero]

end ArkLib.ProximityGap.PeriodMomentLaw

#print axioms ArkLib.ProximityGap.PeriodMomentLaw.rawMoment_erase_zero
