/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The moment-method Gauss-period bound for the smooth domain (#389)

The prize per-frequency core is `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{y∈G} ψ(b·y)` the incomplete subgroup
Gauss sum over the smooth domain `G = μ_n` (`n = 2^μ`). This file packages the **moment method**: the
in-tree `2r`-th moment identity `Σ_b ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`) turns a bound
on the `r`-th additive energy `E_r(G)` directly into a per-frequency bound.

**The named DC-included input (`GaussianEnergyBound`):** `E_r(μ_n) ≤ (2r-1)‼·n^r` — the
**real-Gaussian** energy bound. This is PROVEN in characteristic 0 (Lam–Leung: every vanishing sum of `2^μ`-th roots of
unity decomposes into negation pairs `{ζ^c, ζ^{c+n/2}}`; union bound over the `(2r-1)‼` perfect
matchings of the `2r` exponents, each contributing `n^r`). It transfers to `F_q` whenever char-`p` is
safe, i.e. `q > (2r)^{φ(n)} = (2r)^{n/2}` (then no nonzero `2r`-term `±1` cyclotomic integer `α`,
`|N(α)| ≤ (2r)^{φ(n)}`, vanishes mod `p`). See
`docs/references/proximity-gap-paley-spectrum/README.md` and `memory issue389-gauss-sum-reformulation`.

**Prize-depth correction:** `GaussianEnergyBound` includes the DC frequency `b=0`. At the prize saddle
depth this full-energy hypothesis is false past the `b=0` crossover; see
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`. For the actual nonzero-frequency
house bound at prize depth, use the DC-subtracted formulation in `DCEnergyCorrection.DCEnergyBound`
and `DCSubtractedMoment.sum_nonzero_moment`.

**Consequence (proven here, axiom-clean):** `‖η_b‖^{2r} ≤ q·(2r-1)‼·n^r` for every `b`, hence
`‖η_b‖² ≤ (q·(2r-1)‼·n^r)^{1/r}` — the in-tree open residual `WorstCaseIncompleteSumBound` at scale
`M_r = (q·(2r-1)‼·n^r)^{1/r}`. Minimizing over `r` (optimum `r* ≈ ln q`, using `((2r-1)‼)^{1/2r} ~
√(2r/e)`) gives `B ≤ √(2·n·ln q)` — the Gaussian/Ramanujan per-frequency target, beating the best
*proven* literature bound (BGK `n^{1-o(1)}`). **Honest scope:** this DC-included route is useful before
the DC crossover (and for small/safe transfers), but it is not the prize-depth carrier. The prize-regime
`n = 2^30` (`q = 2^158`) input is the DC-subtracted char-`p` transfer in `DCEnergyCorrection`.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #389.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.GaussPeriodMomentBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The real-Gaussian energy bound** at order `r` (the prize per-frequency input): the `r`-th
additive energy of the smooth domain `G` is bounded by the `2r`-th moment of a real Gaussian of
variance `|G|`, `E_r(G) ≤ (2r-1)‼·|G|^r`. PROVEN char-0 (Lam–Leung + union bound over the `(2r-1)‼`
matchings); holds in `F_q` when char-`p` safe (`q > (2r)^{|G|/2}`). -/
def GaussianEnergyBound (G : Finset F) (r : ℕ) : Prop :=
  (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- **Moment-method per-frequency power bound.** From `GaussianEnergyBound`, every Gauss period
satisfies `‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r`. Proof: a single term is `≤` the full `2r`-th moment
`Σ_b ‖η_b‖^{2r} = q·E_r(G)` (`subgroup_gaussSum_moment`), then apply the energy bound. -/
theorem eta_pow_le_of_energyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_moment hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by ring

/-- **Bridge to the in-tree open residual.** `GaussianEnergyBound` at order `r ≥ 1` discharges
`WorstCaseIncompleteSumBound` at scale `M_r = (q·(2r-1)‼·|G|^r)^{1/r}` (take the `r`-th root of the
power bound). Feeds the interior δ\* consumer chain; minimizing `M_r` over `r` (optimum `r*≈ln q`)
yields the `√(2 n ln q)` Gauss-period bound. -/
theorem worstCaseIncompleteSumBound_of_energyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} (hr : 1 ≤ r) (h : GaussianEnergyBound G r) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) ^ ((r : ℝ)⁻¹)) := by
  intro b _
  set X : ℝ := (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_energyBound hψ h b
  -- ‖η_b‖² = ((‖η_b‖²)^r)^{1/r} ≤ X^{1/r} by rpow monotonicity
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

end ArkLib.ProximityGap.GaussPeriodMomentBound

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.GaussPeriodMomentBound.eta_pow_le_of_energyBound
#print axioms ArkLib.ProximityGap.GaussPeriodMomentBound.worstCaseIncompleteSumBound_of_energyBound
