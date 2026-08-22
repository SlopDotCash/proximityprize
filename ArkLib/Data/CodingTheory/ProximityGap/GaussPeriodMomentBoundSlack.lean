/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The moment method tolerates a POLYNOMIAL slack in the energy bound (#389, #407)

`GaussPeriodMomentBound` discharges the per-frequency core from the **exact** real-Gaussian energy
bound `GaussianEnergyBound : E_r(μ_n) ≤ (2r-1)‼·n^r`. This file records the quantitatively important
observation that the moment method does **not** need the energy at its exact char-0 value: a
*polynomial* slack `S` is harmless, because the bound takes a `2r`-th root.

> **`GaussianEnergyBoundWithSlack G r S : E_r(G) ≤ S·(2r-1)‼·n^r`**  ⟹  `‖η_b‖² ≤ M_r(S)`,
> with `M_r(S) = (q·S·(2r-1)‼·n^r)^{1/r} = S^{1/r}·M_r(1)`.

Hence the per-frequency bound `B = max_b‖η_b‖ ≤ √(M_r(S))` carries only the factor `S^{1/2r}`. At the
optimal depth `r ≈ ln m` (`m = (q-1)/|G|`), `S^{1/2r} = S^{1/(2 ln m)}`; for a **polynomial** slack
`S = n^A` and a polynomial field `q = n^β` (so `ln m = (β-1) ln n`), this is
`exp(A/(2(β-1))) = O(1)` — a *constant* factor on the floor `√(2n ln m)`. So the prize floor (up to a
constant `C`, which only shifts the window's `Θ(1/log n)` term) follows from the **far weaker**
polynomial-slack energy bound `E_r(μ_n) ≤ n^{O(1)}·(2r-1)‼·n^r`, not the exact `(2r-1)‼·n^r`.

This relocates the open core to a *poly-slack higher-energy bound* — strictly weaker than the exact
`GaussianEnergyBound` and than full BGK square-root cancellation. (At `r = 2` it is already KNOWN:
Heath-Brown–Konyagin give `E_2(μ_n) ≤ n^{5/2}` in the prize range `n < p^{1/4}`, i.e. slack `n^{1/2}`
over the diagonal `3n²`. The open part is the uniform poly slack up to `r ≈ ln m`.)

Empirical support (`probe_gp_floor_density_existence.py` + moment-opt probes): the *optimized* bound
`min_r (Σ_i η_i^{2r})^{1/2r}` stays `≤ 1.07·floor` up to `n = 64` even at the worst prime (whose
energy slack is `~n^{1.3}`, crushed to `1.18` by the `2r`-th root). This is recorded as an honest
named conditional, NOT a closure: the uniform poly-slack bound at `r ≈ ln m` is open.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #389, #407.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.GaussPeriodMomentBoundSlack

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The energy bound with a multiplicative slack `S`.** `E_r(G) ≤ S·(2r-1)‼·|G|^r`. The exact
`GaussianEnergyBound` is the `S = 1` case. -/
def GaussianEnergyBoundWithSlack (G : Finset F) (r : ℕ) (S : ℝ) : Prop :=
  (rEnergy G r : ℝ) ≤ S * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- A poly-slack energy bound gives a per-frequency power bound carrying the factor `S`:
`‖η_b‖^{2r} ≤ q·S·(2r-1)‼·|G|^r`. Same proof as `eta_pow_le_of_energyBound` with the slack
threaded through. -/
theorem eta_pow_le_of_energyBound_slack {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} {S : ℝ} (h : GaussianEnergyBoundWithSlack G r S) (b : F) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (S * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' : F, ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) (Finset.mem_univ b)
  rw [subgroup_gaussSum_moment hψ G r] at hterm
  calc ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) := hterm
    _ ≤ (Fintype.card F : ℝ) * (S * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- **Poly-slack bridge to the in-tree open residual.** `GaussianEnergyBoundWithSlack` at order
`r ≥ 1` with slack `S` discharges `WorstCaseIncompleteSumBound` at scale
`M_r(S) = (q·S·(2r-1)‼·|G|^r)^{1/r}`. The slack enters only as `S^{1/r}` in the squared scale, hence
as `S^{1/2r}` in `B = max_b‖η_b‖` — a *constant* factor whenever `S` is polynomial in `|G|` and the
depth is `r ≈ ln m`. -/
theorem worstCaseIncompleteSumBound_of_energyBound_slack {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} {r : ℕ} {S : ℝ} (hr : 1 ≤ r) (hS : 0 ≤ S)
    (h : GaussianEnergyBoundWithSlack G r S) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (S * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
        ^ ((r : ℝ)⁻¹)) := by
  intro b _
  set X : ℝ := (Fintype.card F : ℝ) * (S * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
    with hX
  have hXnn : 0 ≤ X := by
    rw [hX]; positivity
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_of_energyBound_slack hψ h b
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-- **The slack contributes exactly `S^{1/r}` to the squared per-frequency scale.**
`M_r(S) = S^{1/r}·M_r(1)`, making explicit that a polynomial `S = |G|^A` gives only the constant
factor `S^{1/r} = |G|^{A/r}` (→ `exp(A/(β-1))` at `r ≈ ln m`, `|G| = n`, polynomial field). -/
theorem slack_scale_factor (q DF Gr S : ℝ) (hq : 0 ≤ q) (hDF : 0 ≤ DF) (hGr : 0 ≤ Gr)
    (hS : 0 ≤ S) (r : ℕ) :
    (q * (S * (DF * Gr))) ^ ((r : ℝ)⁻¹)
      = S ^ ((r : ℝ)⁻¹) * (q * (DF * Gr)) ^ ((r : ℝ)⁻¹) := by
  rw [show q * (S * (DF * Gr)) = S * (q * (DF * Gr)) by ring,
    Real.mul_rpow hS (by positivity)]

end ArkLib.ProximityGap.GaussPeriodMomentBoundSlack

#print axioms ArkLib.ProximityGap.GaussPeriodMomentBoundSlack.eta_pow_le_of_energyBound_slack
#print axioms ArkLib.ProximityGap.GaussPeriodMomentBoundSlack.worstCaseIncompleteSumBound_of_energyBound_slack
#print axioms ArkLib.ProximityGap.GaussPeriodMomentBoundSlack.slack_scale_factor
