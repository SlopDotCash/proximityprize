/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodFirstMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodRealValued
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodParsevalFloor

/-!
# The EVT / de-Finetti closure route for the BGK floor — substrate hub (#407, CRACK 7)

The crack-audit's top *closure* re-attack (CRACK 7): prove the BGK floor
`M(n) = max_{b≠0}‖η_b‖ ≤ √(2n·log(p/n))(1+o(1))` not as the 25-year analytic √-cancellation wall,
but as an **extreme-value theorem** for the *exchangeable de-Finetti period family*. The periods
`η_b = Σ_{x∈G} ψ(bx)` over the nonzero frequencies are:

1. **mean-pinned** — `Σ_{b≠0} η_b = −|G|` (`_GaussPeriodFirstMoment.subgroup_gaussSum_firstMoment`),
   so the per-frequency mean is `−n/(q−1) ≈ 0`;
2. **variance-pinned** — `Σ_{b≠0} ‖η_b‖² = q·n − n²` (`GaussPeriodParsevalFloor.sum_sq_erase_zero`),
   so the per-frequency variance is `≈ n`;
3. **real** — `conj(η_b) = η_b` for negation-closed `G` (`_GaussPeriodRealValued`), so the family is
   a *real* exchangeable array, and the bulk moments are real-Gaussian (Wick `(2r−1)‼·n^r`,
   `DyadicEnergyK1`).

This hub assembles (1)–(3) as the **de-Finetti two-moment + reality substrate** and states the single
remaining open input as a named `Prop`: the EVT/Gumbel **concentration** of the max of the `m=(q−1)/n`
real exchangeable periods under exactly this two-moment constraint. Together they give the prize floor.

The concentration `EVTConcentration` is the genuine open core (the deep-`r ≈ log m` tail the bulk
Gaussianity does not control) — left named, never asserted (honesty contract). The point of this hub
is that CRACK 7 reframes the prize as a *concrete probability theorem* (Gumbel max of `m` exchangeable
mean/variance-pinned reals), with all the distributional substrate now axiom-clean in-tree.

Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodParsevalFloor
open ProximityGap.Frontier.GaussPeriodFirstMoment
open ProximityGap.Frontier.GaussPeriodRealValued

namespace ProximityGap.Frontier.EVTFloorRoute

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The de-Finetti substrate (assembled, proven).** For a negation-closed `G` with `0 ∉ G` and
primitive `ψ`, the Gauss-period family is mean-pinned (`Σ_{b≠0} η_b = −|G|`) and real
(`conj η_b = η_b`). Together with the Parseval variance `Σ_{b≠0}‖η_b‖² = q·n − n²`
(`sum_sq_erase_zero`, same hypotheses), this is the full two-moment + reality data the EVT route
consumes. -/
theorem deFinetti_substrate {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hG : (0 : F) ∉ G) (hneg : ∀ y ∈ G, -y ∈ G) :
    (∑ b ∈ Finset.univ.erase (0 : F), eta ψ G b = -(G.card : ℂ))
      ∧ (∀ b : F, (starRingEnd ℂ) (eta ψ G b) = eta ψ G b) :=
  ⟨subgroup_gaussSum_firstMoment hψ hG, fun b => eta_conj_eq_of_neg_closed hψ hneg b⟩

/-- **The open EVT input (named, never asserted).** `EVTConcentration ψ G C` asserts the Gumbel-type
concentration the floor needs: every nonzero period is within the `√(2·log(index))` envelope of the
`√n` variance scale, uniformly — `‖η_b‖ ≤ C·√(|G|·log((q)/|G|))`. This is exactly the prize floor /
`NearRamanujanBound`; under the de-Finetti substrate (`deFinetti_substrate`) it is the concentration
of the max of `m` real exchangeable mean/variance-pinned periods. The deep-`r ≈ log m` tail is the
genuine open core (CRACK 7). -/
def EVTConcentration (ψ : AddChar F ℂ) (G : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ G b‖ ≤ C * Real.sqrt ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))

/-- **The route, stated:** the EVT concentration *is* the prize per-frequency floor in squared form
(`‖η_b‖² ≤ C²·n·log(q/n)`), the input the in-tree δ\* consumer chain wants. Trivial unfolding —
records that closing `EVTConcentration` over the de-Finetti substrate closes the floor. -/
theorem prizeFloor_of_EVTConcentration {ψ : AddChar F ℂ} {G : Finset F} {C : ℝ} (hC : 0 ≤ C)
    (hL : 0 ≤ (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card))
    (h : EVTConcentration ψ G C) (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ 2
      ≤ C ^ 2 * ((G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card)) := by
  set L : ℝ := (G.card : ℝ) * Real.log ((Fintype.card F : ℝ) / G.card) with hLdef
  have hb' : ‖eta ψ G b‖ ≤ C * Real.sqrt L := h b hb
  have hbase : 0 ≤ C * Real.sqrt L := mul_nonneg hC (Real.sqrt_nonneg _)
  have hsq := mul_le_mul hb' hb' (norm_nonneg _) hbase
  calc ‖eta ψ G b‖ ^ 2 = ‖eta ψ G b‖ * ‖eta ψ G b‖ := pow_two _
    _ ≤ (C * Real.sqrt L) * (C * Real.sqrt L) := hsq
    _ = C ^ 2 * (Real.sqrt L * Real.sqrt L) := by ring
    _ = C ^ 2 * L := by rw [Real.mul_self_sqrt hL]

end ProximityGap.Frontier.EVTFloorRoute

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.EVTFloorRoute.deFinetti_substrate
#print axioms ProximityGap.Frontier.EVTFloorRoute.prizeFloor_of_EVTConcentration
