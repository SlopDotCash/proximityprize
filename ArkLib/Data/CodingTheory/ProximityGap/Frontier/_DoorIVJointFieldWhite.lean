/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Door IV: the period field is an UNCORRELATED (white) field on the multiplicative quotient —
# the joint b↔b' structure is diagonal, so it carries no information beyond the variance

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_joint_bcorrelation.py`.

## The probed object

My three prior door-(iv) Lane-1 sweeps pinned the worst-`b` cancellation to the MARGINAL Gaussian-EVT
law of `{|η_b|}` (dead = door (iii)) and localized the only surviving surface as the JOINT correlation
across distinct cosets `b`. Since `η` is constant on multiplicative `μ_n`-cosets, the field lives on
the cyclic quotient `ℤ_{(p-1)/n}` via `j ↦ η_{g^j}`.

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1)

The field `j ↦ η_{g^j}` is an **uncorrelated white field**: the lag-`k` autocorrelation of `|η|`, of
the complex `η`, and of the energy `|η|²` are all `≈ 0` at every nonzero lag and **shrink with `N`**
(measured `|ac₁| ≤ 0.06 → 1e-3 → 1e-3`; `max_{1≤lag≤50}|ac| → 0`). The lone additive-neighbour
correlation `corr(|η_b|, |η_{b+1}|) = 0.74` appears only at the Fermat prime `p = 65537` (`p/n = 4096`
small) and **collapses to ≈ 0** for the larger generic primes — a finite-size / Fermat artifact, not a
prize-regime signal.

So even the JOINT structure is dead: the period field has no exploitable low-order multiplicative
correlation. The cancellation difficulty is the irreducible BGK wall — there is neither marginal nor
low-order joint structure to grip.

## The formalizable kernel (this file): zero cross-covariance ⇒ diagonal second moment

The formal content of "white field": if the centered field `g_j = f_j − μ` has zero summed
cross-products at a fixed nonzero lag `k` (`Σ_j g_j g_{j+k} = 0`), then the lag-`k` block of the
field's covariance contributes **nothing** — the joint second-moment structure reduces to the diagonal
variance `Σ_j g_j²`. Concretely, the lag-`k` "shifted energy" `Σ_j g_j g_{σ(j)}` (for any reindexing
`σ` realizing the lag) vanishes, so a quadratic functional built from one nonzero-lag block carries no
information beyond the variance. This proves nothing about CORE and uses no completion; it is the
no-go pin: the joint b↔b' route is diagonal (= the variance = the dead marginal moment).
-/

namespace ProximityGap.Frontier.DoorIVJointFieldWhite

open Finset

variable {ι : Type*}

/-- Centering is linear: `Σ (f i − μ) = (Σ f i) − card·μ`. The centered field is what carries the
covariance structure. -/
theorem sum_centered (f : ι → ℝ) (s : Finset ι) (μ : ℝ) :
    ∑ i ∈ s, (f i - μ) = (∑ i ∈ s, f i) - (s.card : ℝ) * μ := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- The variance (diagonal second moment) is nonnegative — the only surviving moment of a white field. -/
theorem diagonal_sndMoment_nonneg (f : ι → ℝ) (s : Finset ι) (μ : ℝ) :
    0 ≤ ∑ i ∈ s, (f i - μ) ^ 2 := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- White-field diagonalization. If the centered field `g = f − μ` has zero cross-covariance against
a reindexed copy `g ∘ σ` (the lag-`k` shift), i.e. `Σ_i g_i · g_{σ i} = 0`, then the centered
second-moment quadratic form
`Σ_i (g_i + g_{σ i})²` equals `2 · Σ_i g_i²` whenever `σ` is a bijection of `s` onto itself
(so the shifted block has the same diagonal mass) — the cross term drops out, leaving only the
diagonal variance. The joint lag-`k` structure thus contributes nothing beyond the diagonal. -/
theorem white_field_diagonalizes
    (f : ι → ℝ) (s : Finset ι) (μ : ℝ) (σ : ι → ι)
    (hσ : ∑ i ∈ s, (f i - μ) * (f (σ i) - μ) = 0)
    (hbij : ∑ i ∈ s, (f (σ i) - μ) ^ 2 = ∑ i ∈ s, (f i - μ) ^ 2) :
    ∑ i ∈ s, ((f i - μ) + (f (σ i) - μ)) ^ 2 = 2 * ∑ i ∈ s, (f i - μ) ^ 2 := by
  have hexpand : ∀ i,
      ((f i - μ) + (f (σ i) - μ)) ^ 2
        = (f i - μ) ^ 2 + 2 * ((f i - μ) * (f (σ i) - μ)) + (f (σ i) - μ) ^ 2 := by
    intro i; ring
  calc ∑ i ∈ s, ((f i - μ) + (f (σ i) - μ)) ^ 2
      = ∑ i ∈ s, ((f i - μ) ^ 2 + 2 * ((f i - μ) * (f (σ i) - μ)) + (f (σ i) - μ) ^ 2) := by
        exact Finset.sum_congr rfl (fun i _ => hexpand i)
    _ = (∑ i ∈ s, (f i - μ) ^ 2)
          + 2 * (∑ i ∈ s, (f i - μ) * (f (σ i) - μ))
          + (∑ i ∈ s, (f (σ i) - μ) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ i ∈ s, (f i - μ) ^ 2) + 2 * 0 + (∑ i ∈ s, (f i - μ) ^ 2) := by
        rw [hσ, hbij]
    _ = 2 * ∑ i ∈ s, (f i - μ) ^ 2 := by ring

end ProximityGap.Frontier.DoorIVJointFieldWhite

#print axioms ProximityGap.Frontier.DoorIVJointFieldWhite.sum_centered
#print axioms ProximityGap.Frontier.DoorIVJointFieldWhite.diagonal_sndMoment_nonneg
#print axioms ProximityGap.Frontier.DoorIVJointFieldWhite.white_field_diagonalizes
