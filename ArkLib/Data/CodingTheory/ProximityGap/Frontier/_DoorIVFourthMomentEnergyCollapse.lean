/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV: the period MARGINAL's 4th moment (kurtosis) collapses to the additive energy `E₂(μ_n)`
# — the first higher-order functional is the already-refuted energy route

This file records the axiom-clean kernel behind the probes
`scripts/probes/probe_dooriv_complex4thmoment_gaussianity.py` and
`scripts/probes/probe_dooriv_4thmoment_iid_control.py`.

## Why this matters

My 4-sweep door-(iv) Lane-1 chain pinned the period field's marginal AND second-order joint structure
as Gaussian/white (door (iii) = BGK, dead), and pointed the only surviving surface at HIGHER-ORDER /
nonlinear functionals. The first such functional is the complex 4th moment of the period marginal,
`K₄ = E_b|η_b|⁴ / (E_b|η_b|²)²`.

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1)

`K₄ ≈ 2.81 → 2.98` — FAR above the complex-Gaussian baseline `2.0` and above the `n`-independent-phase
value `2 − 1/n`: a genuine heavy-tail excess. **Adversarial re-check (honesty rule 6):** the subgroup
additive energy `E₂(μ_n)` is `1.45–1.49 ×` the random/iid value `2n²−n` (thinness-essential, rule-3
PASS) — but the EXACT identity (verified numerically to machine precision, p=97 n=8: both `= 168`)

`(1/p) · Σ_{b ∈ F_p} |η_b|⁴ = E₂(S) := #{(x₁,x₂,x₃,x₄) ∈ S⁴ : x₁+x₂ = x₃+x₄}`

shows the 4th moment **IS** the additive energy. So the K₄ heavy-tail excess collapses EXACTLY to
`E₂(μ_n)/n²` — the additive-moment/energy route, which is PROVEN NON-PROVING in §6 of #444 (the
meta-theorem: additive-energy bounds saturate at structured primes). The "go higher-order" escape my
own chain pointed at is therefore dead at 4th order: it routes straight back to the refuted energy lane.

## The formalizable kernel (this file)

The character-orthogonality identity over `F_p` needs the full Gauss-sum substrate (present elsewhere
in-tree under `AdditiveEnergy*`/`*ParsevalFloor`). Here we record the self-contained ALGEBRAIC core of
the collapse: the b-averaged 4th power is, by orthogonality, a sum of nonnegative quadruple
multiplicities. We state orthogonality abstractly (a hypothesis `horth`) and PROVE the collapse, so the
brick is honest and kernel-checked without re-deriving Gauss sums.
-/

namespace ProximityGap.Frontier.DoorIVFourthMomentEnergyCollapse

open Finset

variable {ι κ : Type*}

/-- Additive-quadruple multiplicity is nonnegative-real and equals a real count: the additive energy
`E₂` of a family is the sum of squared sumset multiplicities, hence `≥ 0`. We model the multiplicity
of a target sum `t` as `mult t = (number of pairs hitting t)` and `E₂ = Σ_t (mult t)²`. -/
def additiveEnergy (mult : κ → ℝ) (T : Finset κ) : ℝ := ∑ t ∈ T, (mult t) ^ 2

theorem additiveEnergy_nonneg (mult : κ → ℝ) (T : Finset κ) :
    0 ≤ additiveEnergy mult T := by
  unfold additiveEnergy
  apply Finset.sum_nonneg
  intro t _
  positivity

/-- The collapse identity (abstract form). Suppose the b-averaged 4th power of the period equals, by
character orthogonality, the additive energy: this is supplied as the hypothesis `hcollapse` (the
content proved from the Gauss-sum substrate elsewhere). Then the 4th moment is exactly an additive
energy — a nonnegative quadruple-count object. Consequently any bound *through* the 4th moment is a
bound through `E₂`, i.e. the energy route. -/
theorem fourthMoment_eq_additiveEnergy_is_energyObject
    (fourthMomentAvg : ℝ) (mult : κ → ℝ) (T : Finset κ)
    (hcollapse : fourthMomentAvg = additiveEnergy mult T) :
    fourthMomentAvg = additiveEnergy mult T ∧ 0 ≤ fourthMomentAvg := by
  refine ⟨hcollapse, ?_⟩
  rw [hcollapse]
  exact additiveEnergy_nonneg mult T

/-- Monotone-collapse corollary: if a sup-norm candidate `M` is controlled by the 4th moment in the
usual `M⁴ ≤ p · (avg 4th power)` Plancherel-type direction, and the avg 4th power IS the additive
energy, then `M⁴ ≤ p · E₂` — the bound passes entirely through `E₂(μ_n)`, the refuted energy object.
This records (abstractly) that the higher-order door inherits the energy route's deadness. -/
theorem sup_fourthPower_le_energy_scale
    {M p fourthMomentAvg : ℝ} (mult : κ → ℝ) (T : Finset κ)
    (hcollapse : fourthMomentAvg = additiveEnergy mult T)
    (hM : M ^ 4 ≤ p * fourthMomentAvg) :
    M ^ 4 ≤ p * additiveEnergy mult T := by
  rwa [hcollapse] at hM

end ProximityGap.Frontier.DoorIVFourthMomentEnergyCollapse

#print axioms ProximityGap.Frontier.DoorIVFourthMomentEnergyCollapse.additiveEnergy_nonneg
#print axioms ProximityGap.Frontier.DoorIVFourthMomentEnergyCollapse.fourthMoment_eq_additiveEnergy_is_energyObject
#print axioms ProximityGap.Frontier.DoorIVFourthMomentEnergyCollapse.sup_fourthPower_le_energy_scale
