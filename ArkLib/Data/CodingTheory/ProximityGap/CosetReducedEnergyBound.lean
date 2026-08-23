/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The coset-reduced moment-method bound from the energy hypothesis (#407)

`GaussPeriodMomentBound.eta_pow_le_of_energyBound` gives, from `GaussianEnergyBound`
(`E_r(G) ≤ (2r-1)‼·n^r`), the per-frequency bound `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r` (single-term ≤ whole
`2r`-th moment). This file sharpens it by the **coset reduction**
(`GaussPeriodCosetReduction.cosetReduced_eta_pow_le`, which divides by `n` and subtracts the `b=0`
term): for a finite multiplicative subgroup `G = μ_n` and every `b ≠ 0`,

> `‖η_b‖^{2r} ≤ (q·(2r-1)‼·n^r − n^{2r}) / n`.

The `/n` (sum over the `m = (q-1)/n` cosets, not `q` frequencies) is the factor that, after the
`2r`-th root at the optimal depth `r ≈ ln q`, takes the crude moment bound down to the
near-Ramanujan-up-to-√log scale `M ≲ √(2 n ln q)` (`GaussPeriodSpectralFrame.NearRamanujanSqrtLog`),
removing the `n^{1/2r}` log-loss. This is the sharp form of the energy→sup-norm consumer, conditional
on the (named-open, char-`p`) energy input `GaussianEnergyBound`.

Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.CosetReducedEnergyBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Coset-reduced energy → sup-norm bound.** For a finite multiplicative subgroup `G = μ_n`
(`hbij`, `h0`, `hne`) satisfying the energy hypothesis `GaussianEnergyBound G r`, every nonzero
frequency obeys the `n`-fold-sharper bound `‖η_b‖^{2r} ≤ (q·(2r-1)‼·n^r − n^{2r})/n`. Sharpens
`eta_pow_le_of_energyBound` (`≤ q·(2r-1)‼·n^r`) by the coset reduction. -/
theorem cosetReduced_eta_pow_le_of_energyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {r : ℕ} (henergy : GaussianEnergyBound G r) {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖ ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          - (G.card : ℝ) ^ (2 * r)) / (G.card : ℝ) := by
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  -- the coset-reduced bound in terms of rEnergy
  have hcoset := cosetReduced_eta_pow_le hψ hbij h0 hne r hb₀
  -- monotone: q·rEnergy ≤ q·((2r-1)‼·n^r), so the numerators compare, divide by n>0
  have hmono : (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left henergy (by positivity)
  have hnum : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
          - (G.card : ℝ) ^ (2 * r) := by linarith
  exact le_trans hcoset (div_le_div_of_nonneg_right hnum hcardpos.le)

end ArkLib.ProximityGap.CosetReducedEnergyBound

#print axioms ArkLib.ProximityGap.CosetReducedEnergyBound.cosetReduced_eta_pow_le_of_energyBound
