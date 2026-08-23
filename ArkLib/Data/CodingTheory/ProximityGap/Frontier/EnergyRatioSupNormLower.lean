/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.EnergyLogConvexRatioMonotone

/-!
# The energy ratio is a CERTIFIED LOWER BOUND on the spectral sup-norm (#444)

**What this extends.** `EnergyLogConvexRatioMonotone` landed the UPPER direction of the log-convex
energy ladder: `E_{r+1} ≤ (max_b‖η_b‖²)·E_r` (`energy_succ_le_maxSq_mul`), plus the prose conclusion
that the ratio approaches `max‖η‖²` from below. This file lands the COMPLEMENTARY LOWER direction, the
honest/easy companion of the refuted upper-bound route:

> **For every `r`, `max_b‖η_b‖² ≥ E_{r+1}/E_r`** (the spectral max is bracketed FROM BELOW by every
> consecutive additive-energy ratio), and by the proven ratio-monotonicity the bound TIGHTENS with `r`.

This is the rearrangement of `energy_succ_le_maxSq_mul` into the form
`max_b λ_b ≥ (∑ λ_b^{r+1})/(∑ λ_b^r)` with `λ_b = ‖η_b‖²`, a *lower* bound on the prize quantity
`M(n)² = max_{b≠0}‖η_b‖²` rather than the wall-bearing upper bound. It is the standard
"moments-pin-the-max-from-below" fact specialised to the proven Gauss-period moment ladder.

## What is PROVEN here (axiom-clean `{propext, Classical.choice, Quot.sound}`)

* `maxSq_ge_energy_ratio` (HEADLINE), for the full spectrum: if `0 < E_r` and `M` is any spectral
  upper certificate (`∀ b, ‖η_b‖² ≤ M`), then the per-step ratio satisfies `(E_{r+1}:ℝ)/E_r ≤ M`.
  Equivalently `M ≥ E_{r+1}/E_r`: NO certificate `M` can sit below any energy ratio. The ratio form
  of the in-tree `energy_succ_le_maxSq_mul` (needs `0 < E_r`).
* `sum_succ_le_mul_sum`, the abstract rearrangement on ANY nonnegative finite spectrum
  `λ : ι → ℝ`, `M` an entrywise upper bound: `∑ λ_i^{t+1} ≤ M·∑ λ_i^t`. Reusable for the `b≠0`
  restricted spectrum (the prize-relevant DC-subtracted ratio).
* `restricted_ratio_le_maxSq`, the prize-relevant form on `b ≠ 0`: with `M` an upper bound on the
  NON-principal spectrum (`∀ b ∈ s, ‖η_b‖² ≤ M`), the restricted ratio
  `(∑_{b∈s}‖η_b‖^{2(r+1)})/(∑_{b∈s}‖η_b‖^{2r}) ≤ M`. Taking `s = {b ≠ 0}` and `M = M(n)²` this is the
  certified lower bound on the prize sup-norm `M(n)²` from the DC-subtracted energies `A_r`.

## Honesty / scope (rules 1,3,6 + ASYMPTOTIC GUARD)

NOT a CORE closure: a LOWER bound on `M(n)` is the easy/honest direction (the WALL is the matching
UPPER bound `M(n) ≤ C√(n log(p/n))`, untouched). Principal-spike caveat: the FULL-spectrum max is the
trivial principal `‖η_0‖² = n²`, and the full ratio `E_{r+1}/E_r → n²` (the `b=0` term dominates the
moments), so the full-max lower bound is true but converges to the trivial `n²`. The genuinely
prize-relevant statement is the RESTRICTED form on `b ≠ 0` (`restricted_ratio_le_maxSq`), whose limit
is the prize `M(n)² = max_{b≠0}‖η_b‖²`. This brick makes NO capacity / beyond-Johnson claim and does
NOT touch the cliff-at-n/2 (it is a lower bound, structurally orthogonal to the over-det face).

Field-universal structural identity (it holds for the thick group too); its CONSEQUENCE for the prize
is thinness-essential only through the VALUE of `max_{b≠0}‖η_b‖²` (which it bounds from below, not
above). By rule 3 it cannot prove the thinness-essential prize, and it does not pretend to: it bounds
the prize quantity from the WRONG (easy) side.

Probe `scripts/probes/probe_energy_ratio_supnorm_lower.py` (PROPER subgroups `μ_n ⊊ 𝔽_p^*`, `n=2^a`,
primes `p` incl. prize-regime `p=65537, n=16, β=4`, NEVER `n=q-1`): `0 fails/9`. For every `r`,
`max‖η‖² ≥ E_{r+1}/E_r`, ratios monotone (corroborating the in-tree `energy_ratio_monotone_nat`).

## References
- `EnergyLogConvexRatioMonotone` (the proven log-convex ladder this extends).
- `MomentSupNormBridge.sup_le_moment_root` (the single-moment-root UPPER companion; this is the
  ratio-level LOWER companion, sharper in the limit).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ProximityGap.Frontier.EnergyRatioSupNormLower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Abstract rearrangement on any nonnegative finite spectrum.** For `λ : ι → ℝ` nonnegative on a
finset `s` and `M` an entrywise upper bound (`∀ i ∈ s, λ i ≤ M`), the `(s+1)`-st power sum is at most
`M` times the `s`-th: `∑_{i∈s} (λ i)^{t+1} ≤ M·∑_{i∈s} (λ i)^t`. (Pull the max out of
`λ^{t+1} = λ·λ^t`.) Reusable on the NON-principal spectrum `{b ≠ 0}`. -/
theorem sum_succ_le_mul_sum {ι : Type*} (s : Finset ι) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) (M : ℝ) (hM : ∀ i ∈ s, lam i ≤ M) (t : ℕ) :
    (∑ i ∈ s, (lam i) ^ (t + 1)) ≤ M * (∑ i ∈ s, (lam i) ^ t) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hstep : (lam i) ^ (t + 1) = lam i * (lam i) ^ t := by rw [pow_succ]; ring
  rw [hstep]
  exact mul_le_mul_of_nonneg_right (hM i hi) (pow_nonneg (hnn i hi) t)

/-- **HEADLINE, the energy ratio is a lower bound on the spectral max (ratio form).** If `M` is any
spectral upper certificate (`∀ b, ‖η_b‖² ≤ M`) and `0 < E_r`, then the per-step energy ratio satisfies
`(E_{r+1} : ℝ)/E_r ≤ M`, i.e. `M ≥ E_{r+1}/E_r`. So NO certificate can sit below any consecutive
additive-energy ratio: `max_b‖η_b‖²` is bounded BELOW by every `E_{r+1}/E_r`. (Division form of the
in-tree `energy_succ_le_maxSq_mul`.) -/
theorem maxSq_ge_energy_ratio {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b : F, ‖eta ψ G b‖ ^ 2 ≤ M) (hEr : 0 < (rEnergy G r : ℝ)) :
    (rEnergy G (r + 1) : ℝ) / (rEnergy G r : ℝ) ≤ M := by
  have hceil :=
    ProximityGap.Frontier.EnergyLogConvexRatio.energy_succ_le_maxSq_mul hψ G r M hM
  rw [div_le_iff₀ hEr]
  exact hceil

/-- **Prize-relevant restricted form (the DC-subtracted ratio).** On the NON-principal spectrum
`s ⊆ 𝔽_p` (intended `s = {b ≠ 0}`), with `M` an upper bound on `‖η_b‖²` over `s` and the restricted
`r`-th power sum positive, the restricted ratio is `≤ M`:

    `(∑_{b∈s} ‖η_b‖^{2(r+1)}) / (∑_{b∈s} ‖η_b‖^{2r}) ≤ M`.

Taking `s = {b≠0}`, `M = M(n)² = max_{b≠0}‖η_b‖²`, the restricted power sums are the DC-subtracted
energies `q·A_r = ∑_{b≠0}‖η_b‖^{2r}`, so this is the certified lower bound
`M(n)² ≥ A_{r+1}/A_r` on the PRIZE sup-norm (the limit of these ratios is exactly `M(n)²`). The honest
EASY direction; the matching upper bound is the wall. -/
theorem restricted_ratio_le_maxSq {ψ : AddChar F ℂ} (G : Finset F) (s : Finset F) (r : ℕ)
    (M : ℝ) (hM : ∀ b ∈ s, ‖eta ψ G b‖ ^ 2 ≤ M)
    (hpos : 0 < ∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * r)) :
    (∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * (r + 1))) / (∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * r)) ≤ M := by
  rw [div_le_iff₀ hpos]
  -- reindex `‖η‖^{2(r+1)} = (‖η‖²)^{r+1}`, `‖η‖^{2r} = (‖η‖²)^r`, apply the abstract rearrangement
  have hnn : ∀ b ∈ s, 0 ≤ ‖eta ψ G b‖ ^ 2 := fun b _ => by positivity
  have hkey := sum_succ_le_mul_sum s (fun b => ‖eta ψ G b‖ ^ 2) hnn M hM r
  have hL : (∑ b ∈ s, (‖eta ψ G b‖ ^ 2) ^ (r + 1))
      = ∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * (r + 1)) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← pow_mul]
  have hR : (∑ b ∈ s, (‖eta ψ G b‖ ^ 2) ^ r) = ∑ b ∈ s, ‖eta ψ G b‖ ^ (2 * r) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← pow_mul]
  rw [hL, hR] at hkey
  exact hkey

end ProximityGap.Frontier.EnergyRatioSupNormLower

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.EnergyRatioSupNormLower.sum_succ_le_mul_sum
#print axioms ProximityGap.Frontier.EnergyRatioSupNormLower.maxSq_ge_energy_ratio
#print axioms ProximityGap.Frontier.EnergyRatioSupNormLower.restricted_ratio_le_maxSq
