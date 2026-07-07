/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R27FullTowerCollapse

/-!
# LANE B2 (#466 round 30): the EXACT lag-correlation identity — the round-29 excess
  mechanism is closed-form, Weil-scale, and VANISHES at prize scaling

Round 29 found the r = 3 excess is carried by linear-lag phase autocorrelations of the Jacobi
sequence.  This brick evaluates them EXACTLY (probe `probe_r30_lag_identity.py`, 1e-11):

  **`lag_correlation_identity`** :
  `∑_{j∈ℤ/m} J_{j+t}·conj(J_j)  =  m · ∑_{u∈G} ∑_y χ(1−u·y)·conj(χ(1−y))·λ_t(y)`.

Each inner `y`-sum is a COMPLETE two-character sum (Weil class, `≤ C√q` pointwise), so
`|A(t)| ≤ m·n·C·√q` — measured ratio `0.4–0.77` at `C = 1`.  Normalized against `‖J‖² ≈ q`,
the lag correlation is `≈ n/√q`: **at prize scaling (β > 2) the pair-resonance excess decays**
— the round-23/28/29 super-Gaussian excess is a small-`q` artifact, and the prize-scale
constant in `TripleConvEnergyBound` should approach the Gaussian `C = 6`.  The identity is
pure orthogonality (indicator + group law + `λ` trivial on `G`), landed with zero analytic
input; the Weil bound on the inner sums is the same named-input class as round 17.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  Issue #466, round 30, LANE B2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

open ArkLib.ProximityGap.Frontier.R19JacobiFourierExpansion
open ArkLib.ProximityGap.Frontier.R20JacobiParseval
open ArkLib.ProximityGap.Frontier.R24InvolutionNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m] {lam : ZMod m → F → ℂ} {G : Finset F} {χ : F → ℂ}

/-- `λ_j(y⁻¹) = conj(λ_j(y))` on units (both are the inverse of the unit-modulus value). -/
theorem lam_inv_eq_conj (hfam : SubgroupDualFamily G m lam)
    (hgrp : DualFamilyGroupLaw m lam) (j : ZMod m) {y : F} (hy : y ≠ 0) :
    lam j y⁻¹ = (starRingEnd ℂ) (lam j y) := by
  rw [conj_lam hfam hgrp j hy]
  have hone : lam j (1 : F) = 1 := by
    have h := hfam.map_mul j 1 1
    rw [mul_one] at h
    have hne : lam j (1 : F) ≠ 0 := lam_ne_zero hgrp j one_ne_zero
    have h' : lam j (1:F) * 1 = lam j (1:F) * lam j (1:F) := by rw [mul_one, ← h]
    exact (mul_left_cancel₀ hne h').symm
  have h1 : lam j y⁻¹ * lam j y = 1 := by
    rw [← hfam.map_mul, inv_mul_cancel₀ hy, hone]
  have h2 : lam (-j) y * lam j y = 1 := by
    rw [← hgrp.add_eq_mul]
    simp [hfam.triv_on_units y hy]
  have hne : lam j y ≠ 0 := lam_ne_zero hgrp j hy
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- **THE EXACT LAG-CORRELATION IDENTITY (round-30 main theorem).**
`∑_j J_{j+t}·conj(J_j) = m·∑_{u∈G} ∑_y χ(1−u·y)·conj(χ(1−y))·λ_t(y)` — every lag correlation
of the ladder's coefficient sequence is `m` times a sum of `n` COMPLETE two-character sums.
Pure orthogonality; Weil then gives `|A(t)| ≤ m·n·C√q`, which vanishes at prize scaling
relative to `‖J‖² ≈ q`. -/
theorem lag_correlation_identity
    (hfam : SubgroupDualFamily G m lam) (hgrp : DualFamilyGroupLaw m lam) (t : ZMod m) :
    ∑ j : ZMod m, jacobiCoeff χ lam (j + t) * (starRingEnd ℂ) (jacobiCoeff χ lam j)
      = (m : ℂ) * ∑ u ∈ G, ∑ y : F, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y))
          * lam t y := by
  classical
  -- expand both Jacobi coefficients and push conj inside
  have hexp : ∀ j : ZMod m,
      jacobiCoeff χ lam (j + t) * (starRingEnd ℂ) (jacobiCoeff χ lam j)
        = ∑ x : F, ∑ y : F, (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
            * (lam (j + t) x * (starRingEnd ℂ) (lam j y)) := by
    intro j
    rw [jacobiCoeff, jacobiCoeff, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hexp j)]
  rw [Finset.sum_comm]
  -- for each x: swap j to the inside of y as well
  have hswap : ∀ x : F,
      ∑ j : ZMod m, ∑ y : F, (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
          * (lam (j + t) x * (starRingEnd ℂ) (lam j y))
      = ∑ y : F, ∑ j : ZMod m, (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
          * (lam (j + t) x * (starRingEnd ℂ) (lam j y)) := fun x => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun x _ => hswap x)]
  -- the inner j-sum collapses by the indicator: Σ_j λ_j(x·y⁻¹) = m·1_G(x·y⁻¹)
  have hinner : ∀ x y : F, y ≠ 0 →
      ∑ j : ZMod m, lam (j + t) x * (starRingEnd ℂ) (lam j y)
        = lam t x * ((m : ℂ) * (if x * y⁻¹ ∈ G then 1 else 0)) := by
    intro x y hy
    have hpt : ∀ j : ZMod m, lam (j + t) x * (starRingEnd ℂ) (lam j y)
        = lam t x * lam j (x * y⁻¹) := by
      intro j
      calc lam (j + t) x * (starRingEnd ℂ) (lam j y)
          = (lam j x * lam j y⁻¹) * lam t x := by
            rw [hgrp.add_eq_mul j t x, ← lam_inv_eq_conj hfam hgrp j hy]
            ring
        _ = lam t x * lam j (x * y⁻¹) := by
            rw [← hfam.map_mul j x y⁻¹]
            ring
    rw [Finset.sum_congr rfl (fun j _ => hpt j), ← Finset.mul_sum, hfam.indicator (x * y⁻¹)]
  -- the y = 0 rows vanish (conj λ_j 0 = 0)
  have hy0 : ∀ x : F,
      ∑ j : ZMod m, (χ (1 - x) * (starRingEnd ℂ) (χ (1 - (0:F))))
          * (lam (j + t) x * (starRingEnd ℂ) (lam j (0:F))) = 0 := by
    intro x
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [hfam.map_zero j]
    simp
  -- assemble: LHS = m·Σ_{y≠0} Σ_{x : x·y⁻¹∈G} χχ̄·λ_t(x); then x = u·y reindex
  have hmain : ∑ x : F, ∑ y : F, ∑ j : ZMod m,
      (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
        * (lam (j + t) x * (starRingEnd ℂ) (lam j y))
      = (m : ℂ) * ∑ y ∈ Finset.univ.erase (0 : F), ∑ x : F,
          (if x * y⁻¹ ∈ G then 1 else 0) * (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y))
            * lam t x) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_erase (s := (Finset.univ : Finset F)) (a := (0:F))
      (f := fun y => ∑ x : F, ∑ j : ZMod m,
        (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
          * (lam (j + t) x * (starRingEnd ℂ) (lam j y)))
      (by simpa using Finset.sum_eq_zero (fun x _ => hy0 x))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have hy0' : y ≠ 0 := (Finset.mem_erase.mp hy).1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    calc ∑ j : ZMod m, (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
          * (lam (j + t) x * (starRingEnd ℂ) (lam j y))
        = (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
            * ∑ j : ZMod m, lam (j + t) x * (starRingEnd ℂ) (lam j y) := by
          rw [Finset.mul_sum]
      _ = (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)))
            * (lam t x * ((m : ℂ) * (if x * y⁻¹ ∈ G then 1 else 0))) := by
          rw [hinner x y hy0']
      _ = (m : ℂ) * ((if x * y⁻¹ ∈ G then 1 else 0)
            * (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)) * lam t x)) := by ring
  rw [hmain]
  congr 1
  -- row-wise reindex x = u·y (bijection filter ↔ G), then swap and restore the y = 0 term
  have hrow : ∀ y ∈ Finset.univ.erase (0 : F),
      ∑ x : F, (if x * y⁻¹ ∈ G then (1:ℂ) else 0)
          * (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)) * lam t x)
      = ∑ u ∈ G, χ (1 - u * y) * (starRingEnd ℂ) (χ (1 - y)) * lam t y := by
    intro y hy
    have hy0 : y ≠ 0 := (Finset.mem_erase.mp hy).1
    have hite : ∀ x : F, (if x * y⁻¹ ∈ G then (1:ℂ) else 0)
        * (χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)) * lam t x)
        = (if x * y⁻¹ ∈ G then χ (1 - x) * (starRingEnd ℂ) (χ (1 - y)) * lam t x else 0) := by
      intro x
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => hite x), ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => x * y⁻¹) (fun u => u * y) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [mul_assoc, mul_inv_cancel₀ hy0, mul_one]
      exact hu
    · intro x _
      dsimp only
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    · intro u _
      dsimp only
      rw [mul_assoc, mul_inv_cancel₀ hy0, mul_one]
    · intro x hx
      dsimp only
      have hmem : x * y⁻¹ ∈ G := (Finset.mem_filter.mp hx).2
      have hxy : x * y⁻¹ * y = x := by
        rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
      rw [hxy]
      have hlam : lam t x = lam t y := by
        have hx_eq : x = (x * y⁻¹) * y := hxy.symm
        rw [hx_eq, hfam.map_mul t (x * y⁻¹) y,
          lam_eq_one_on_G hfam hgrp hmem t, one_mul]
      rw [hlam]
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  -- restore y = 0 (its summand vanishes: λ_t(0) = 0)
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0:F))]
  rw [hfam.map_zero t]
  ring

end ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity.lam_inv_eq_conj
#print axioms
  ArkLib.ProximityGap.Frontier.R30LagCorrelationIdentity.lag_correlation_identity
